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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHiW64T10

/-
# Caustic `r = 1024` Halo-16 Walk `w64` Part `11` (`FindAllJohnsonRampKickMuxHiW64T11`)

Certifies part `11` of `w_hi64_m64_r1024` (`m = 64`) halo-16 trajectory.
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

/-- Generator list for `w64_s5`. -/
def rkmHbWin_w64_s5 : List ℤ := altBuildHbFrom 1856 1024 19586394833 0 1024
/-- Entry `rkmXsWin_w64_s5_in`. -/
def rkmXsWin_w64_s5_in : List ℤ := let p := rkmP; let n := rkmN; [p 208475749, p 386014885,
  p 525333499, p 455252394, p 35298947, n 715660460, n 1855818299, n 3223716549, n 4253275202,
  n 4232268483, n 2394487412, p 2482418525, p 10863091018, p 22547258948, p 36082717707,
  p 47755387050, p 51639115495, p 39527302265, p 1346751471, n 72896147310, n 190375855259,
  n 351709745780, n 545808339397, n 743561960009, n 892485334325, n 910406485342, n 681192365555,
  n 53131098634, p 1160199295956, p 3174848092231, p 6226956981310, p 10559333073392,
  p 16404700593234, p 23965808988182, p 33395075751257, p 44775036613076, p 58101146947046,
  p 73269359079508, p 90070447563239, p 108190189748895, p 127218429847025, p 146665028896870,
  p 165981868733857, p 184590379525564, p 201911715468875, p 217397344078097, p 230557880596850,
  p 240988729520037, p 248389733532730, p 252577774748094, p 253492496193230, p 251194670802832,
  p 245856745432672, p 237748944731940, p 227220131203274, p 214675991337184, p 200556385446120,
  p 185313079971181, p 169389094260290, p 153200782215716, p 137124129857374, p 121484447607337,
  p 106549700496227, p 92528508621575, p 79570979824947, p 67771845276927, p 57176159911061,
  p 47786675916372, p 39570828273556, p 32468947922410, p 26401691198462, p 21277038518749,
  p 16996080494740, p 13458013419912, p 10564505444230, p 8222261558362, p 6345008745819,
  p 4855198198630, p 3684313517836, p 2772654459695, p 2069360143248, p 1531855710058,
  p 1124780751493, p 819115650123, p 591652744755, p 423832021960, p 301160860410, p 212087432296,
  p 147969569060, p 102337756620, p 70029753905, p 47269417547, p 31471144421, p 20639132786,
  p 13200932185, p 8115778866, p 4744917810, p 2590661298, p 1223150569, p 380758498]
/-- Exit `rkmXsWin_w64_s5_out`. -/
def rkmXsWin_w64_s5_out : List ℤ := let p := rkmP; let n := rkmN; [n 374066155, n 256635584,
  p 316093828, p 851626877, p 834437856, n 31150220, n 1213632546, n 1923937504, n 1229038287,
  p 928946222, p 3428612016, p 4114332387, p 1665630631, n 3174726309, n 7520243095, n 7836959792,
  n 2268127540, p 7562926358, p 15959338423, p 16033029293, p 4180994364, n 15637974809,
  n 32623264318, n 33593135538, n 11315628926, p 28208983227, p 65106386106, p 73766021127,
  p 36851138184, n 39792650079, n 122814469624, n 162736865687, n 118047566588, p 17679954816,
  p 199046952688, p 337807144403, p 337635013865, p 144831666935, n 208117621915, n 591643747870,
  n 814311585891, n 699497951960, n 178123597622, p 644553665115, p 1483686916623, p 1949717951287,
  p 1691003150120, p 556733198556, n 1279573461635, n 3297530744915, n 4736332769567,
  n 4817881930033, n 3028663091931, p 627686680570, p 5497211366205, p 10325313784614,
  p 13503005264282, p 13463233334122, p 9135644238303, p 341745558937, n 11977519958425,
  n 25771805671950, n 38143956262821, n 45815613581202, n 45703536533241, n 35486063637412,
  n 14046043829978, p 18292352226281, p 59772527993948, p 107445107413695, p 157583978301063,
  p 206194087199282, p 249520945743988, p 284481624577311, p 308959675153659, p 321940548810442,
  p 323488975547051, p 314598736410929, p 296955632625471, p 272662574635015, p 243968618171992,
  p 213036466584467, p 181768084981383, p 151696486226299, p 123940765259639, p 99212553624876,
  p 77861784370407, p 59943502909453, p 45294506023263, p 33607304310878, p 24495509121011,
  p 17545257547203, p 12353725833206, p 8553085090781, p 5824343727120, p 3901649615089,
  p 2571642908846, p 1667862902354, p 1064501624077, p 668501953513, p 413105854728,
  p 251044068314, p 149999930868, p 87949966149, p 50598346352, p 28413913299, p 15542990555,
  p 8088228433, p 3928266152, p 1597601973, p 481815816]
/-- Generator list for `w64_s6a`. -/
def rkmHbWin_w64_s6a : List ℤ := altBuildHbFrom 1856 1024 19587930735 0 1024
/-- Entry `rkmXsWin_w64_s6a_in`. -/
def rkmXsWin_w64_s6a_in : List ℤ := let p := rkmP; let n := rkmN; [n 374066155, n 256635584,
  p 316093828, p 851626877, p 834437856, n 31150220, n 1213632546, n 1923937504, n 1229038287,
  p 928946222, p 3428612016, p 4114332387, p 1665630631, n 3174726309, n 7520243095, n 7836959792,
  n 2268127540, p 7562926358, p 15959338423, p 16033029293, p 4180994364, n 15637974809,
  n 32623264318, n 33593135538, n 11315628926, p 28208983227, p 65106386106, p 73766021127,
  p 36851138184, n 39792650079, p 122814469625, p 162736865688, p 118047566589, p 17679954816,
  p 199046952688, n 337807144402, n 337635013864, n 144831666934, p 208117621916, p 591643747871,
  p 814311585892, p 699497951961, p 178123597623, p 644553665115, p 1483686916623, p 1949717951287,
  p 1691003150120, p 556733198556, p 1279573461636, p 3297530744916, p 4736332769568,
  p 4817881930034, p 3028663091932, p 627686680570, p 5497211366205, p 10325313784614,
  p 13503005264282, p 13463233334122, p 9135644238303, n 341745558936, p 11977519958426,
  p 25771805671951, p 38143956262822, p 45815613581203, p 45703536533242, p 35486063637413,
  p 14046043829979, p 18292352226281, p 59772527993948, p 107445107413695, p 157583978301063,
  p 206194087199282, p 249520945743988, p 284481624577311, p 308959675153659, p 321940548810442,
  p 323488975547051, p 314598736410929, p 296955632625471, p 272662574635015, p 243968618171992,
  p 213036466584467, p 181768084981383, p 151696486226299, p 123940765259639, p 99212553624876,
  p 77861784370407, p 59943502909453, p 45294506023263, p 33607304310878, p 24495509121011,
  p 17545257547203, p 12353725833206, p 8553085090781, p 5824343727120, p 3901649615089,
  p 2571642908846, p 1667862902354, p 1064501624077, p 668501953513, p 413105854728,
  p 251044068314, p 149999930868, p 87949966149, p 50598346352, p 28413913299, p 15542990555,
  p 8088228433, p 3928266152, p 1597601973, p 481815816]
/-- Exit `rkmXsWin_w64_s6a_out`. -/
def rkmXsWin_w64_s6a_out : List ℤ := let p := rkmP; let n := rkmN; [p 249138697, n 741109905,
  p 1543834932, n 2754362496, p 4265686389, n 6063715620, p 8311236338, n 10809259950,
  p 13703353593, n 17015377430, p 20603137864, n 24457163413, p 28637420652, n 32855614006,
  p 36897181398, n 40725271584, p 43806343112, n 45855731971, p 46557607285, n 45526824884,
  p 42335763401, n 36938445750, p 29386416396, n 19748277395, p 8663503192, p 3017292629,
  n 14454380774, p 24273046577, n 31148480872, p 33816427061, n 31194793804, p 22214602067,
  n 6584706599, n 15341962995, p 42895111721, n 74507459679, p 107946109523, n 141023498309,
  p 171637873702, n 198287724675, p 220569915318, n 239915875510, p 258857649710, n 281057631752,
  p 310823328871, n 351735952656, p 405464130717, n 470913896529, p 543899363842, n 617127334709,
  p 680931575381, n 725784308573, p 743568729973, n 729126193540, p 681156114792, n 602054592137,
  p 496526635902, n 370173983571, p 228809311241, n 78766608477, n 72781443963, p 216463482446,
  n 339351872510, p 425744602666, n 459411663245, p 427828894076, n 325388673808, p 155816037641,
  p 66864642788, n 319157940100, p 569770108288, n 780651046555, p 909045686077, n 911622025323,
  p 753834071713, n 425393563858, n 43132381891, p 569883447727, n 1028573091433, p 1277824416019,
  n 1209368493648, p 798439035116, n 133755669722, n 594312725575, p 1151087309469,
  n 1343086924787, p 1097955649257, n 500659265867, n 233595596470, p 841063388390,
  n 1112697625857, p 973583379859, n 505747362870, n 92431381048, p 588906425061, n 808803153127,
  p 697449781936, n 334378579648, n 105661845962, p 430182870365, n 515056681655, p 361130157756,
  n 88272858505, n 137071280946, p 204333131604, n 127401393160, p 25287632127, n 20521941927,
  p 126717684800, n 221622529849, p 145280917873, p 141450868921, n 473336118047, p 569348514025,
  n 256637356018, n 341174958090, p 828977864747, n 804503631811, p 186056012626, p 660361245511,
  n 1134047360367, p 832647096386, p 109480087919, n 1057017316754, p 1300678484545,
  n 591785835301, n 616451978308, p 1441316604840, n 1210332826357, p 15441667574, p 1271946281944,
  n 1617608824958, p 660257175989, p 904928298533, n 1798254547006, p 1201673040317,
  p 469288403660, n 1808858584468, p 1597215545236, p 64114572821, n 1730710071520,
  p 1857280856823, n 251943390786, n 1640312428830, p 2016381931816, n 449952559344,
  n 1596334910530, p 2106869991180, n 513012952957, n 1634500583070, p 2140003203545,
  n 425884967212, n 1760837903132, p 2097367399114, n 179295953074, n 1944487422622,
  p 1939272100202, p 214090051183, n 2122139269682, p 1630060507557, p 710515722805,
  n 2221962413149, p 1157404593533, p 1252981776479, n 2185189695138, p 515428193232,
  p 1792098724255, n 1938241794025, n 324995652903, p 2238068936196, n 1330967037682,
  n 1353429998997, p 2338057257514, n 190034190798, n 2307311144273, p 1667617898981,
  p 1367100045931, n 2523555487107, p 22614060903, p 2554359222388, n 1339616523092,
  n 1890508451852, p 2207579661361, p 856076397380, n 2480476266486, p 192429839705,
  p 2218692090723, n 981937814922, n 1605601189151, p 1370025426108, p 856241210172,
  n 1335827821521, n 150177670585, p 941572414291, n 402127185607, n 288059125998, p 762742579484,
  n 519805508149, n 951484144050, p 1393618322440, p 1023606814210, n 2269651546764,
  n 1049885336095, p 3109550178565, p 1104122423488, n 3895223211935, n 1260259154042,
  p 4617673543137, p 1595700791819, n 5258764568233, n 2192432760771, p 5766759747723,
  p 3127584399965, n 6032068538442, n 4447698875796, p 5872303563303, p 6124350649366,
  n 5036324600931, n 7990497344043, p 3245350108622, p 9663834604743, n 306505116120,
  n 10499919485560, n 3673908138281, p 9682362583749, p 8043415801085, n 6554068464389,
  n 11532983726869, p 1116744498621, p 12574079431565, p 5620330977926, n 9908533436346,
  n 11664000724949, p 3197033218973, p 14277421770571, p 6246874931618, n 10633630571675,
  n 14423433144930, p 95140522410, p 15212156150563, p 12488393942146, n 5214267905800,
  n 17631909420089, n 10558552130916, p 8652275409196, p 19608447670689, p 10521531068414,
  n 10103262054669, n 22341962074266, n 14023348534441, p 8323516142589, p 25652975213431,
  p 22839805843712, p 969243378935, n 23729345594614, n 32192422431375, n 16169023473139,
  p 16207200178983, p 45708009689851, p 53813566875176, p 33526636371011, n 6589051522566,
  n 46442411758450, n 63590660839303, n 42713789002976, p 18706780484359, p 110212514341596,
  p 212829660567502, p 305698532942978, p 372152370582520, p 403372460107534, p 399043659624334,
  p 365575285754373, p 313063346988637, p 252202890335492, p 191992400504360, p 138562050878989,
  p 95028588078027, p 62036517503939, p 38595108697409, p 22899570982058, p 12962619424280,
  p 7000711828685, p 3605963782383, p 1770140392009, p 827137669135, p 367228714767,
  p 154276998670, p 60994332400, p 22383078193, p 7409775553, p 1937571270, p 275001115]

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
  match Nat.sub Q P with
  | 0 => Nat.add v (Nat.div (Nat.sub P Q) d)
  | k + 1 => Nat.sub v (Nat.div (Nat.add k 1) d)
private theorem svEq (z v P Q d : ℕ) (hv : 0 < bSV v P Q d) :
    ((bSV v P Q d : ℤ) - (z : ℤ)) = ((v : ℤ) - (z : ℤ)) + zTdiv ((P : ℤ) - (Q : ℤ)) d := by
  rw [← sntEq]; unfold bSV at hv ⊢; unfold rkmUltraSubNatTdiv
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
private def uCN4 (x1 x2 x3 x4 : ℕ) (xs : List ℕ) : List ℕ :=
  match Nat.add 1 x1 with
  | 0 => xs
  | v1 + 1 => match Nat.add 1 x2 with
    | 0 => xs
    | v2 + 1 => match Nat.add 1 x3 with
      | 0 => xs
      | v3 + 1 => match Nat.add 1 x4 with
        | 0 => xs
        | v4 + 1 => match xs with
          | [] => [v1, v2, v3, v4]
          | h :: t => v1 :: v2 :: v3 :: v4 :: h :: t
private theorem uCN4e (x1 x2 x3 x4 : ℕ) (xs : List ℕ) :
    uCN4 x1 x2 x3 x4 xs = uCN x1 (uCN x2 (uCN x3 (uCN x4 xs))) := by
  unfold uCN4; rw [n1a x1, n1a x2, n1a x3, n1a x4]
  rw [uCN_eq, uCN_eq, uCN_eq, uCN_eq]; cases xs <;> rfl
private def bAP4 : List ℕ → Bool
  | a :: b :: c :: d :: xs =>
    cond (Nat.ble a 0) false (cond (Nat.ble b 0) false
      (cond (Nat.ble c 0) false (cond (Nat.ble d 0) false (bAP4 xs))))
  | xs => bAP xs
private theorem bAP4e : ∀ (xs : List ℕ), bAP4 xs = bAP xs
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | _ :: _ :: _ :: _ :: xs => by dsimp only [bAP4, bAP]; rw [bAP4e xs]
private def bChkP (out : List ℕ) : Option (List ℕ) :=
  match out with
  | [] => some []
  | x :: xs => cond (bAP4 (x :: xs)) (some (x :: xs)) none
private theorem bChkPe (out : List ℕ) : bChkP out = cond (bAP out) (some out) none := by
  cases out with | nil => rfl | cons _ _ => dsimp only [bChkP]; rw [bAP4e]
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
private def toH4 : List ℕ → HbZ4
  | b1 :: z1 :: b2 :: z2 :: b3 :: z3 :: b4 :: z4 :: bs =>
    match toH4 bs with
    | HbZ4.tail l => HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 (HbZ4.tail l)
    | HbZ4.c4 a1 a2 a3 a4 a5 a6 a7 a8 t =>
      HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 (HbZ4.c4 a1 a2 a3 a4 a5 a6 a7 a8 t)
  | bs => HbZ4.tail bs
private theorem hbz4L_toH4 : ∀ (xs : List ℕ), hbz4L (toH4 xs) = xs
  | [] => rfl | [_] => rfl | [_, _] => rfl | [_, _, _] => rfl
  | [_, _, _, _] => rfl | [_, _, _, _, _] => rfl
  | [_, _, _, _, _, _] => rfl | [_, _, _, _, _, _, _] => rfl
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: bs => by
    have ih := hbz4L_toH4 bs; dsimp only [toH4]
    cases h : toH4 bs with
    | tail _ => rw [h] at ih; dsimp only [hbz4L, hbz4C] at ih ⊢; rw [ih]
    | c4 _ _ _ _ _ _ _ _ _ => rw [h] at ih; dsimp only [hbz4L, hbz4C] at ih ⊢; rw [ih]
private def bSlZ4Step (z d b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) (bR : HbZ4)
    (ih : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _ => []
  | 1, p0, q0, vs, cs => bSlZ z d 1 p0 q0 (hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L bR)) vs cs
  | 2, p0, q0, vs, cs => bSlZ z d 2 p0 q0 (hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L bR)) vs cs
  | 3, p0, q0, vs, cs => bSlZ z d 3 p0 q0 (hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L bR)) vs cs
  | rem + 4, p0, q0, v1 :: v2 :: v3 :: v4 :: vR, c1 :: c2 :: c3 :: c4 :: c5 :: cR =>
    uCN4 (bSV v1 (Nat.add p0 z1) (Nat.add (Nat.mul b1 c2) q0) d)
      (bSV v2 (Nat.add (Nat.mul b1 c1) z2) (Nat.add (Nat.mul b2 c3) z1) d)
      (bSV v3 (Nat.add (Nat.mul b2 c2) z3) (Nat.add (Nat.mul b3 c4) z2) d)
      (bSV v4 (Nat.add (Nat.mul b3 c3) z4) (Nat.add (Nat.mul b4 c5) z3) d)
      (ih rem (Nat.mul b4 c4) z4 vR (c5 :: cR))
  | rem + 4, p0, q0, vs, cs =>
    bSlZ z d (rem + 4) p0 q0 (hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L bR)) vs cs
private def bSlZ4 (z d : ℕ) : HbZ4 → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ
  | HbZ4.tail l => fun rem p0 q0 vs cs => bSlZ z d rem p0 q0 l vs cs
  | HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR =>
    bSlZ4Step z d b1 z1 b2 z2 b3 z3 b4 z4 bR (bSlZ4 z d bR)
private theorem bSlZ4_eq (z d : ℕ) : ∀ (hbz : HbZ4) (rem p0 q0 : ℕ) (vs cs : List ℕ),
    bSlZ4 z d hbz rem p0 q0 vs cs = bSlZ z d rem p0 q0 (hbz4L hbz) vs cs
  | HbZ4.tail _, _, _, _, _, _ => by dsimp only [bSlZ4, hbz4L]
  | HbZ4.c4 _ _ _ _ _ _ b4 z4 bR, rem, _, _, vs, cs => by
    dsimp only [bSlZ4, hbz4L, hbz4C]; match rem with
    | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl
    | rem1 + 4 => match vs with
      | [] => rfl | [_] => rfl | [_, _] => rfl | [_, _, _] => rfl
      | _ :: _ :: _ :: _ :: vR => match cs with
        | [] => rfl | [_] => rfl | [_, _] => rfl | [_, _, _] => rfl | [_, _, _, _] => rfl
        | _ :: _ :: _ :: c4 :: c5 :: cR =>
          dsimp only [bSlZ4Step]; have hr : rem1 + 4 = (((rem1 + 1) + 1) + 1) + 1 := by omega
          rw [hr]; dsimp only [bSlZ, bHO]; rw [uCN4e]
          exact congrArg (fun r => uCN _ (uCN _ (uCN _ (uCN _ r))))
            (bSlZ4_eq z d bR rem1 (Nat.mul b4 c4) z4 vR (c5 :: cR))
private def bDg (z dg mL cL : ℕ) (h4 : HbZ4) (v c : List ℕ) : Option (List ℕ) :=
  fN (rkmNextLen mL cL) fun nL => fN (Nat.mul dg wdScale) fun d =>
    bChkP (bSlZ4 z d h4 nL 0 0 v c)
private theorem bDg_sound (z dg mL cL : ℕ) (b v c out : List ℕ)
    (h : bDg z dg mL cL (toH4 (mkHbZ z b)) v c = some out) :
    bD z out = rkmUltraHornerStage dg mL cL (uHb b) (bD z v) (bD z c) := by
  have hsl := bSlZ_eq z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z b v c
  have hz0 : Nat.mul 0 z = 0 := by rw [Nat.mul_eq]; omega
  rw [hz0] at hsl; unfold bDg at h; dsimp only [fN] at h
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq, bChkPe, bSlZ4_eq, hbz4L_toH4, hsl] at h; revert h
  cases hp : bAP (bSl z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z b v c) with
  | false => intro h; dsimp only [cond] at h; cases h
  | true =>
    intro h; dsimp only [cond] at h; injection h with h'; subst h'; unfold rkmUltraHornerStage
    rw [rkmb_forceNat_eq, rkmb_forceNat_eq, ← bM0 z]; exact bSl_sound z _ _ 0 z b v c hp
private def bBdD (z g m c : ℕ) (h4 : HbZ4) (v x : List ℕ)
    (k : ℕ → List ℕ → Option (List ℕ)) : Option (List ℕ) :=
  fN (rkmNextLen m c) fun n => match bDg z g m c h4 v x with | none => none | some o => k n o
private theorem bBdD_sound {z g m c : ℕ} {b v x out : List ℕ}
    {kB : ℕ → List ℕ → Option (List ℕ)} {kU : ℕ → List ℤ → List ℤ}
    (h : bBdD z g m c (toH4 (mkHbZ z b)) v x kB = some out)
    (hk : ∀ m0, kB (rkmNextLen m c) m0 = some out → bD z out = kU (rkmNextLen m c) (bD z m0)) :
    bD z out = (HighDForce.withForcedNat (rkmNextLen m c) fun nL =>
      HighDForce.withForcedList
        (rkmUltraHornerStage g m c (uHb b) (bD z v) (bD z x)) (kU nL)) := by
  unfold bBdD at h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h; revert h
  cases hs : bDg z g m c (toH4 (mkHbZ z b)) v x with
  | none => intro h; dsimp only at h; cases h
  | some mid =>
    intro h; rw [rkmb_forceNat_eq, rkmb_forceList_eq, ← bDg_sound z g m c b v x mid hs]
    exact hk mid h
private def bSp (z m c : ℕ) (hbz v : List ℕ) : Option (List ℕ) :=
  fH4 (toH4 hbz) fun h4 =>
    bBdD z 16 m c h4 v v fun l x => bBdD z 15 m l h4 v x fun l x =>
    bBdD z 14 m l h4 v x fun l x => bBdD z 13 m l h4 v x fun l x =>
    bBdD z 12 m l h4 v x fun l x => bBdD z 11 m l h4 v x fun l x =>
    bBdD z 10 m l h4 v x fun l x => bBdD z 9 m l h4 v x fun l x =>
    bBdD z 8 m l h4 v x fun l x => bBdD z 7 m l h4 v x fun l x =>
    bBdD z 6 m l h4 v x fun l x => bBdD z 5 m l h4 v x fun l x =>
    bBdD z 4 m l h4 v x fun l x => bBdD z 3 m l h4 v x fun l x =>
    bBdD z 2 m l h4 v x fun l x => bDg z 1 m l h4 v x
private theorem bSp_sound (z mL cL : ℕ) (b v out : List ℕ)
    (h : bSp z mL cL (mkHbZ z b) v = some out) :
    bD z out = rkmUltraHornerT16Step mL cL (uHb b) (bD z v) := by
  unfold bSp at h; rw [fH4e] at h; unfold rkmUltraHornerT16Step
  refine bBdD_sound h fun _ h => bBdD_sound h fun _ h => bBdD_sound h fun _ h => ?_
  refine bBdD_sound h fun _ h => bBdD_sound h fun _ h => bBdD_sound h fun _ h => ?_
  refine bBdD_sound h fun _ h => bBdD_sound h fun _ h => bBdD_sound h fun _ h => ?_
  refine bBdD_sound h fun _ h => bBdD_sound h fun _ h => bBdD_sound h fun _ h => ?_
  refine bBdD_sound h fun _ h => bBdD_sound h fun _ h => bBdD_sound h fun _ h => ?_
  exact bDg_sound z 1 mL _ b v _ out h
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
private theorem bAllT_hd {b : Bool} {bs : List Bool} (h : bAllT (b :: bs) = true) :
    b = true := by
  cases b with
  | false => exact Bool.noConfusion h
  | true => rfl
private theorem bAllT_tl {b : Bool} {bs : List Bool} (h : bAllT (b :: bs) = true) :
    bAllT bs = true := by
  cases b with
  | false => exact Bool.noConfusion h
  | true => exact h
private theorem bTl4 {a b c d : Bool} {bs : List Bool}
    (h : bAllT (a :: b :: c :: d :: bs) = true) : bAllT bs = true :=
  bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl h)))
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
private def rkmPhb_w64_s5 : List ℕ := uNatCatN
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
    635538523440875,634738632400929,633935846426426,633130161776402,632321574650999],
   [631510081190912,630695677476829,629878359528867,629058123305992,628234964705438,
    627408879562108,626579863647972,625747912671455,624913022276811,624075188043494,
    623234405485513,622390670050778,621543977120442,620694322008220,619841699959710,
    618986106151697,618127535691445,617265983615981,616401444891364,615533914411947,
    614663386999622,613789857403058,612913320296920,612033770281084,611151201879831,
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
    492459459799133,491177273507590,489890606869225,488599433910581,487303728258387],
   [486003463131788,484698611334393,483389145246106,482075036814759,480756257547529,
    479432778502126,478104570277763,476771603005881,475433846340638,474091269449139,
    472743841001415,471391529160127,470034301569998,468672125346958,467304967066994,
    465932792754694,464555567871480,463173257303510,461785825349244,460393235706668,
    458995451460151,457592435066931,456184148343218,454770552449897,453351607877814,
    451927274432641,450497511219296,449062276625900,447621528307261,446175223167874,
    444723317344393,443265766187590,441802524243758,440333545235543,438858782042187,
    437378186679162,435891710277157,434399303060419,432900914324390,431396492412650,
    429885984693098,428369337533382,426846496275518,425317405209673,423782007547093,
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
    243614756926474,240878143701519,238110473612025,235310670372914,232477592819083],
   [229610029322772,226706691578216,223766207663733,220787114275844,217767848011414,
    214706735551208,211601982570821,208451661171369,205253695581116,202005845828166,
    198705689020949,195350597793716,191937715374060,188463926602120,184925824068014,
    181319668323357,177641340848093,173886288092327,170049454431923,166125201229537,
    162107208311199,157988352951503,153760559755203,149414612395204,144939914648452,
    140324182971264,135553045000879,130609506211139,125473227601428,120119525523793,
    114517950653104,108630207037182,102406992908535,95782990012395,88668472556053,80934244623273,
    72381987847174,62677810015780,51170580129421,36179035075236]]
private def rkmPhb_w64_s6a : List ℕ := uNatCatN
  [
   [627458078945719,626628998022825,625796981807391,624962025943332,624124126009753,
    623283277520311,622439475922561,621592716597292,620742994857853,619890305949468,
    619034645048545,618176007261962,617314387626359,616449781107400,615582182599037,
    614711586922756,613837988826814,612961382985460,612081763998144,611199126388719,
    610313464604623,609424773016049,608533045915104,607638277514956,606740461948960,
    605839593269775,604935665448465,604028672373589,603118607850266,602205465599239,
    601289239255906,600369922369353,599447508401357,598521990725380,597593362625540,
    596661617295575,595726747837775,594788747261910,593847608484129,592903324325849,
    591955887512619,591005290672964,590051526337218,589094586936323,588134464800622,
    587171152158619,586204641135725,585234923752978,584261991925744,583285837462394,
    582306452062956,581323827317744,580337954705964,579348825594298,578356431235454,
    577360762766700,576361811208363,575359567462311,574354022310397,573345166412885,
    572332990306836,571317484404476,570298638991529,569276444225517,568250890134033,
    567221966612980,566189663424780,565153970196542,564114876418211,563072371440661,
    562026444473776,560977084584472,559924280694701,558868021579404,557808295864427,
    556745092024409,555678398380608,554608203098706,553534494186561,552457259491911,
    551376486700048,550292163331431,549204276739263,548112814107013,547017762445891,
    545919108592278,544816839205097,543710940763136,542601399562312,541488201712888,
    540371333136629,539250779563895,538126526530683,536998559375605,535866863236802,
    534731423048795,533592223539271,532449249225802,531302484412494,530151913186567,
    528997519414859,527839286740263,526677198578078,525511238112287,524341388291760,
    523167631826362,521989951182989,520808328581509,519622745990617,518433185123601,
    517239627434007,516042054111216,514840446075919,513634783975483,512425048179226,
    511211218773574,509993275557113,508771198035523,507544965416400,506314556603959,
    505079950193606,503841124466394,502598057383339,501350726579609,500099109358572,
    498843182685700,497582923182334,496318307119291,495049310410322,493775908605406,
    492498076883883,491215790047421,489929022512802,488637748304534,487341941047275,
    486041573958073,484736619838403,483427051066002,482112839586505,480793956904852],
   [479470374076485,478142061698310,476808989899429,475471128331616,474128446159562,
    472780912050839,471428494165611,470071160146066,468708877105554,467341611617440,
    465969329703651,464591996822897,463209577858584,461822037106373,460429338261402,
    459031444405147,457628317991900,456219920834878,454806214091919,453387158250773,
    451962713113959,450532837783188,449097490643317,447656629345836,446210210791858,
    444758191114598,443300525661328,441837168974776,440368074773958,438893195934422,
    437412484467877,435925891501181,434433367254675,432934861019828,431430321136166,
    429919694967464,428402928877163,426879968202991,425350757230750,423815239167231,
    422273356112234,420725049029646,419170257717543,417608920777273,416040975581479,
    414466358241015,412885003570716,411296845053959,409701814805972,408099843535844,
    406490860507157,404874793497200,403251568754698,401621110955973,399983343159493,
    398338186758712,396685561433133,395025385097510,393357573849110,391682041912918,
    389998701584724,388307463171954,386608234932168,384900923009082,383185431366012,
    381461661716608,379729513452733,377988883569354,376239666586281,374481754466605,
    372715036531646,370939399372248,369154726756205,367360899531631,365557795526035,
    363745289440884,361923252741396,360091553541295,358250056482247,356398622607680,
    354537109230651,352665369795430,350783253732418,348890606306017,346987268455011,
    345073076625024,343147862592556,341211453280069,339263670561587,337304331058171,
    335333245922655,333350220612917,331355054652949,329347541380905,327327467683258,
    325294613714107,323248752598617,321189650119488,319117064385235,317030745478990,
    314930435086401,312815866101090,310686762206003,308542837428811,306383795669386,
    304209330197175,302019123116089,299812844794318,297590153256208,295350693533086,
    293094096969582,290819980481676,288527945762290,286217578429830,283888447114599,
    281540102477433,279172076154332,276783879620140,274375002963573,271944913564978,
    269493054667224,267018843828998,264521671248428,262000897943538,259455853774279,
    256885835288967,254290103375688,251667880696671,249018348880570,246340645444192,
    243633860411091,240897032589740,238129145468473,235329122677809,232495822963161,
    229628034601756,226724469186805,223783754689044,220804427690247,217784924664680],
   [214723572161895,211618575716778,208468007279268,205269790914853,202021686475986,
    198721270881101,195365916558420,191952766511517,188478705336250,184940325355538,
    181333886827762,177655270909905,173899923694996,170062789162454,166138228232770,
    162119920236369,158000741889301,153772617163075,149426329007881,144951280369744,
    140335186741744,135563674634086,130619748187956,125483066807819,120128944910110,
    114526930781961,108638725468147,102415023335092,95790501005980,88675425652092,80940591226068,
    72387663809537,62682725007772,51174592761507,36181872118644]]
private theorem rkmStatOk_hiw64t11 : bAllT [
  muxIntListEq (uHb rkmPhb_w64_s5) (altBuildHbFrom 1856 1024 19586394833 564 460),
  muxIntListEq (uHb rkmPhb_w64_s6a) (altBuildHbFrom 1856 1024 19587930735 709 315),
  Nat.ble (Nat.add 580 (altIntLen rkmXsWin_w64_s5_in)) (Nat.add 1024 1)
  ] = true := by decide +kernel
private theorem rkmHhb_w64_s5 :
    uHb rkmPhb_w64_s5 = rkmDropInts 564 rkmHbWin_w64_s5 :=
  (muxIntListEq_eq_true.mp
    (bAllT_hd rkmStatOk_hiw64t11)).trans
    (drHb 1856 1024 19586394833 564 1024)
private theorem rkmHhb_w64_s6a :
    uHb rkmPhb_w64_s6a = rkmDropInts 709 rkmHbWin_w64_s6a :=
  (muxIntListEq_eq_true.mp
    (bAllT_hd (bAllT_tl rkmStatOk_hiw64t11))).trans
    (drHb 1856 1024 19587930735 709 1024)
private def rkmC_w64_s5_1 : List ℤ := pzigCat
  [
   [699565636,1742732996,2661846436,3337971966,2878218110,559639550,3854638747,10150506569,
    17535505735,23413462905,24230829461,15690621679,6440128952,45039509032,98796791048,
    160308080532,214856131426,238120071274,197666535010,56685673912,220351282261,656892354269,
    1250720914921,1959106875847,2681864258815,3245921911659,3393513144703,2777836412379,
    965432730069,2550142771070,8323764894028,16923682504894,28889240720068,44682074981108,
    64635654872640,88910542515562,117456278957360,149985850612682,185967705482544,
    224634655573130,265010776098212,305955802815512,346222832671104,384525520278234,
    419608301906084,450316317662010,475657866455452,494855438224102,507381359878374,
    512978031021120,511660276341448,503699534582676,489597041550714,470043690830772,
    445872899006028,418009901008650,387421294452552,355068299748134,321865058523238,
    288644376432168,256134649085320,224942737353934,195546799215612,168297166236654,
    143422870599040,121043081911020,101181816394766,83784043542242,68734225513218,55871377973728,
    45004615765512,35927246254118,28427244783300,22296108786572,17336095188292,13363793509728,
    10214236630302,7741357023794,5818090737582,4336399253628,3205495914330,2349972889668,
    1708826444624,1232318938452,881255618830,624973687738,439363114648,306102397812,211339176016,
    144222716390,97288620186,64659437312,42131936312,26890475124,16642356284,9803069020,
    5486943778,2825509362,1008351656,250383556]]
private def rkmC_w64_s5_2 : List ℤ := pzigCat
  [
   [328241743,846314613,1224010197,1100795017,140806533,1773664650,4442143360,7380770188,
    8915415862,7881498416,2754735642,7753107677,23019989637,40345224223,54785598299,58435468631,
    42155206049,2932825966,81322231748,190115763552,315164430706,426983042208,480625626800,
    419089637526,178869161536,296724228249,1040906840973,2042578458081,3224010401525,
    4419941487837,5360161171377,5660828602037,4828705330761,2275370343533,2651979831642,
    10626513025734,22288543417262,38185339474422,58710212890138,84047724170122,114129126484670,
    148606805452226,186847427567786,227947275579586,270771590950350,314010971244844,
    356253775620662,396066869465828,432078932382152,463058814663346,487984069473278,
    506092158385100,516914807801588,520291070425376,516359846979864,505535516221870,
    488468427056300,465993706307870,439076302374010,408751852653752,376071272749100,
    342052171888554,307636218509548,273658166417316,240824683335960,209702904574842,
    180717985031092,154159599916072,130192098871036,108870995557952,90160985103818,
    73954439362526,60090677558194,48373118132584,38583558006994,30496713955880,23889363399504,
    18547954777746,14274884065620,10891151524300,8238232191504,6178539281556,4594748035466,
    3388120803682,2477664125876,1796757872580,1292023755186,921437275694,651545992390,
    456545640186,316977931872,217969184750,148106757528,99592069360,66002323536,42918293388,
    27419581552,17024225350,10048725848,5591649398,2812781780,969594094,231756070]]
private def rkmC_w64_s5_3 : List ℤ := pzigCat
  [
   [476829460,591433412,331635034,637253459,1940647823,3084308447,3738138419,3052072997,10689417,
    5130989260,11645178256,17901425800,20728943878,16973407806,3181424072,21664255915,
    55294326177,91129100053,117173636129,117027751523,73786058053,26450444318,187881523262,
    398050750884,622643890454,802282398518,854202460088,681665788326,188210601502,699375201527,
    2002203007399,3660474407417,5503616367811,7228780643883,8389924838751,8401892888283,
    6562761789453,2094846913885,5799267885214,17866876956332,34729616222268,56811117857374,
    84271588978942,116961581627006,154397986135404,195766397531190,239951195813726,
    285592260498942,331161276499372,375053526304712,415686074416580,451592691855280,
    481511241063342,504452203567238,519746629366434,527070917403188,526447205762838,
    518219987972262,503016352933756,481690997821810,455261830575644,424844844872416,
    391588725026600,356616396853000,320976074953014,285603264309418,251293749985638,
    218690512203976,188279290844310,160393412851866,135227371652306,112853161503458,
    93240668332602,76279388156006,61799379990566,49589946495890,39418025009956,31041512743324,
    24220566379000,18727071515060,14349755832972,10897913492564,8203745484152,6121917778926,
    4528958247472,3321683585184,2415634626010,1741642510460,1244903632096,882298071510,
    619695625964,431192864182,297298028684,202942095470,136933185586,91256303878,60087237304,
    38660874736,24386363152,14982297864,8639486922,4549787204,2116295942,683760534]]
private def rkmC_w64_s5_4 : List ℤ := pzigCat
  [
   [592101614,1495791624,1895486302,1797039788,658749076,1836946187,5034211405,7972848163,
    9176692615,6802873343,394064494,12177247470,26806406086,39453550992,43892844672,33212447474,
    1860115978,50768831063,118105388175,184896259929,226694875755,213272707185,116017471927,
    84644814448,387111475954,758323784298,1127634252752,1385993377382,1394134719632,
    1002150944840,77990793216,1455228134255,3577267430265,6132343813077,8798175953805,
    11069050847571,12262229351779,11545169984701,7988289404601,638771395977,11391358536418,
    28831089680550,52159703527182,81531038513746,116721986720818,157110498415606,201688538163600,
    249109880137506,297765591301086,345885373273344,391651172223354,433314184406506,
    469304986390108,498327729787088,519429956874972,532044853478972,536005161688784,
    531527321644686,519171678148224,499785416519868,474429994750658,444304758957108,
    410670808269396,374780655819740,337817134233970,300846703526950,264786003314750,
    230381177719460,198202228881126,168647571215914,141955922213100,118226620102380,
    97442067827110,79491950956672,64196938230364,51332025081134,40645162430964,31873556663354,
    24757761350146,19050454740768,14522977528376,10970136998440,8211539161392,6091428488316,
    4478473788426,3263490123232,2357295594488,1687554132208,1197452566792,842217437844,
    586802278810,404971373564,276900281152,187351290052,125229732388,82672396640,53794448016,
    34261502458,21120078752,12703301566,7099910776,3479098180,1457472650,432736282]]
private def rkmC_w64_s5_5 : List ℤ := pzigCat
  [
   [594550315,881542221,846209411,195865992,1873839070,3660923800,5013294186,4567920152,
    1472416002,4234447091,11625230147,18061174819,20081916781,14168728909,1648422292,26899286670,
    56168183956,79897679732,85546935804,59926418414,5144157477,107903624349,232764332513,
    347689262737,406807013487,358345291279,157633581337,217357746482,747264515296,1358641333624,
    1918553074300,2240100236494,2104778215040,1299473698492,334952701995,2847603462465,
    6121747728945,9831395416019,13416943582577,16087599358431,16856678302657,14609469369139,
    8195994150499,3454555480298,21214413151210,45645763482412,76908791383378,114703060076732,
    158249652797070,206317132848568,257288868802224,309266964873256,360201264067690,
    408029857204224,450818888212686,486889846452806,514919548846128,534010356223788,
    543724084134858,544079573298824,535518553285802,518845554574162,495149169917502,
    465712182734472,431920920555070,395179870466512,356835453923826,318115884821484,
    280087979156274,243629746957014,209418818048632,177936511036576,149480280224614,
    124185220911768,102050090184884,82965784969254,66743156639994,53138424078718,41876856957706,
    32671654156300,25238189678682,19305881092894,14625992100022,10975303331410,8158278721956,
    6007761455756,4383329269866,3168771430172,2269638628088,1610782749028,1132656390220,
    789185378088,544520359376,372004173216,251763892874,168477590858,111182624378,72379382380,
    46436240976,29089458604,17541892860,10068627374,5397032606,2503789986,768688068]]
private def rkmC_w64_s5_6 : List ℤ := pzigCat
  [
   [324689976,719125962,622169092,200238112,991373559,2405731085,3005010801,2368165741,41888975,
    4083936698,8472962716,11203658386,10011776656,3249306226,9201556201,24496265035,37276014921,
    40664080029,27461476119,5651244542,55446062230,110858653540,152286770108,155532817940,
    98688313734,29155322511,219327090315,436401705099,618395222953,684458573389,551428597143,
    157226171477,510803221276,1391671586462,2336481716398,3108532984380,3406845985172,
    2911769730562,1348736202396,1434614835093,5391024456953,10209925118857,15279886711347,
    19687440916281,22259468943999,21649359620513,16459398623845,5385912104509,12626439513302,
    38244097931564,71633788925256,112396425477902,159553962898776,211594596733632,
    266569693330152,322231091648538,376197387505270,426128844481802,469893404551144,
    505710129805088,532256593638814,548733278776358,554882905627602,550967031816388,
    537707081732986,516197613111408,487802434781960,454045704745014,416506899940286,
    376725406938800,336123423976226,295948567001816,257237685122860,220798566602930,
    187211046993966,156841489413282,129865992842622,106300953743202,86036074635534,
    68867408234934,54528133761926,42714753980404,33109622613856,25399129510888,19285888151318,
    14496747321566,10788406021142,7949752949084,5801091283654,4192256333452,3000397747152,
    2126844746520,1493304884202,1038421951716,714987674514,487345817798,328821240348,
    219530528834,144824708766,94177576132,60205493938,37738861430,23082073372,13571328630,
    7373628336,3369437176,995923920,200029674]]
private def rkmC_w64_s5_7 : List ℤ := pzigCat
  [
   [451862805,582994411,453850569,440578726,1545067202,2236739836,1938043828,381742044,
    2472635009,5565092471,7133118963,5794349943,515880011,8205586522,17629437906,23288706310,
    20605428884,6447851476,18934180287,49293680349,73217649391,77090443027,48373517993,
    17669278284,112140783140,210671217582,275747459530,264207985872,141805029034,101455141707,
    436999350591,791242819963,1050070046191,1078234241065,752817082923,4280597947,1142017549572,
    2535276153514,3890181877910,4808658334570,4834977704586,3539751867038,625420309522,
    3964621927829,9954469354533,16677903599273,23070935799361,27725227134725,29000060016111,
    25182676759945,14679611166989,3785226217456,30991930489296,67090092818274,111526815122152,
    163046586093920,219764582133382,279305509823272,338990009811018,396046869390366,
    447829227685918,492011918790334,526749685921808,550784607317984,563497568698502,
    564903851862032,555597439619306,536657398149040,509528020453014,475888103357196,
    437519167773562,396186761594536,353541448329424,311043447277454,269913737892600,
    231109182083820,195320297715612,162987035183840,134326013709034,109366287270002,
    87989299074340,69967842008768,55002281143600,42752602897348,32864288819238,24988286023252,
    18795969291418,13988685402640,10302336181288,7509013977526,5416850100984,3867858699734,
    2734080817270,1913329585448,1325415644396,908683208116,616507067146,413945153408,
    274990372556,180548583172,116905553478,74422831386,46400609774,28177263196,16505144094,
    9150040508,4619241556,1949831806,537458808]]
private def rkmC_w64_s5_8 : List ℤ := pzigCat
  [
   [926937151,1702126321,1939121711,1056026121,1035936718,3483617388,5184771724,4814439536,
    1177918542,5079282235,11597117655,15330812995,12734548639,1635275927,16260517392,35164429420,
    46219324764,39855160866,10254069544,39774605235,96803762373,138048900837,137393850027,
    74293046927,54349581400,225761249922,389338361334,475411485996,412794137166,154444228510,
    294868314835,860306848759,1394586670001,1697646220915,1559454311537,821181952959,
    557911931132,2446330750012,4513697608246,6246277682792,7013935616618,6182999866610,
    3260363711152,1953374307007,9230671871981,17832017486527,26492412406215,33491478007805,
    36803973781131,34315872881285,24079761742601,4572980795775,25078282901716,64939358231718,
    114195234081116,171177715171058,233487081912440,298191742491658,362080906918492,
    421938981476740,474809607734792,518221870537734,550357626216894,570147280414528,
    577291750201744,572217087268102,555973703779872,530096388977902,496444161554770,
    457038072582758,413911162371452,368981053776356,323952593653764,280253845788458,
    239004003674086,201008712186988,166777415832504,136557100812400,110376265106072,
    88092952727628,69441932091810,54077906702044,41612950380322,31647017036166,23790974378588,
    17682446132232,12995497751630,9445483947702,6790233815914,4828514876502,3396610525208,
    2363817443246,1627572732820,1108711706234,747120513138,497882495906,327947676346,
    213337088686,136876435074,86420483960,53496078198,32277005320,18812334912,10450229672,
    5417783674,2527187592,981104030,250913780]]
private def rkmC_w64_s5_9 : List ℤ := pzigCat
  [
   [679554774,1402812296,1340333368,68993858,1966669365,3795623933,4490389171,2861313041,
    1598429082,7215368144,11129429260,10536767674,3356216760,9671582909,23716791585,31361168935,
    25476162063,2743263665,33003222772,69375869296,87798416010,70486954798,9460933424,
    86316732071,187830690897,250168183281,226542776367,88263240073,156718985596,452683744884,
    699052571226,772556184136,566085405224,34408475252,766288673519,1660062222233,2367217784593,
    2559287315073,1946427822649,380332749741,2052774266662,4977525334816,7736571457480,
    9471800497282,9276705223686,6399241234650,459370591062,8361597688401,19201349787759,
    30499337291537,40098175028427,45457748523131,43955034371517,33227587176733,11510314879465,
    22085742219566,67395380820922,123147817167290,187047707865114,255975816319736,
    326280840438394,394122369904892,455820112271412,508167703234856,548678564353906,
    575743066746418,588688786937438,587748055160778,573947781240934,548943666346262,
    514823520284362,473903368861994,428536759372216,380952875760152,333133319685736,
    286731129001950,243030693038920,202942790168844,167028317975102,135540950720978,
    108482923851678,85663265632386,66756439412978,51353404829002,39005418218122,29258815433950,
    21679474116542,15869988931824,11479310234804,8205940944590,5797808351436,4049287903502,
    2795867975818,1908420189670,1287747167464,858979255074,566340539194,368778808474,
    236987468952,149921505686,93433416758,57115163638,34013606904,19709373434,11015274040,
    5748474284,2651365004,990964948,239547778]]
private def rkmC_w64_s5_10 : List ℤ := pzigCat
  [
   [357965206,67335446,479567615,947166619,1038331825,124096979,1796897272,3467905830,3529227992,
    1364215574,2866368373,7579357155,9712737039,6574044885,2143070788,13614472068,22211962862,
    21365972786,7140938574,18271084609,45300205695,59242296695,46250410969,1270452707,
    65822579616,129418766156,154755092560,111671457334,8583680691,180905109157,345181477971,
    420159195345,331683375527,48413846565,388309971694,855122312152,1167142293942,1128925319778,
    606391060628,400338369701,1709706445043,2960953597069,3677273183249,3385423114665,
    1768870339313,1182245263806,5070857833386,9080048734332,12071345239562,12787896290696,
    10136441432950,3493342330982,7027385031329,20408313569397,34711111407751,47224528456755,
    54767313002999,54101959158033,42395759874651,17655009724155,20939466340346,72846413341808,
    136155335376658,207753739690236,283640904623026,359339899990056,430349145191352,
    492570776988468,542667211925014,578308142912476,598292540102236,602543622258364,
    591997174228666,568407648572906,534105967591144,491743791598460,444050551306160,
    393626391743456,342784195177358,293445826165826,247091551203700,204755467799154,
    167055479412800,134250049837156,106306530326184,82974830051598,63856801886966,48468958997070,
    36293661993994,26816969261576,19556452996040,14078611491744,10006719457874,7023497261690,
    4868501643290,3333463180392,2254438639292,1506028091476,993741653822,647366647174,
    416164357088,263875664654,164854298098,101193980900,61119290132,35994735134,20589929072,
    11351454968,5803183354,2579460872,912083976,206594920]]
private def rkmC_w64_s5_11 : List ℤ := pzigCat
  [
   [234280535,181042598,914231854,1301843326,666097844,1056298241,2842967037,3321020707,
    1467919365,2427943500,6761376400,8392857774,4988058698,3546620215,13559233843,19353510037,
    15110494785,1064367618,24010456812,42108235850,41849008542,15724040694,31948665661,
    82500540189,107511885095,81507721933,2945806476,123961639646,231383249270,262162501392,
    167277363666,57897314847,354191219403,604745643593,668647495583,438273870531,101469319896,
    833298413448,1511504141724,1820239755548,1479032331426,365871715870,1383921864491,
    3343226106879,4854173568577,5184931939327,3754373476515,368724196897,4601650541694,
    10170218154832,14842956561660,16892502687998,14751092137244,7446936584886,5015343023711,
    21422666574941,39335743584071,55310304115803,65330393809243,65384863570389,52088631830947,
    23239287446369,21784056480744,81848214345194,154138480070328,234460607567910,317716589036350,
    398476255562134,471557268787598,532535521144568,578127479565824,606405858574262,
    616846089690874,610219506031632,588368644840536,553907338659424,509895545248652,
    459525619148196,405853633275060,351596139348102,298996489651470,249761875405126,
    205059815382598,165560739243716,131510030270194,102817823186804,79149832911588,
    60013805164806,44833953560372,33009529980160,23958196618342,17145818429820,12101397293854,
    8425005945034,5786732447032,3921648190224,2622468012558,1730501482652,1126492779182,
    723457176502,458089454916,285817832084,175666098214,106051089978,62903623334,36325914030,
    20385288066,10957952034,5371902836,2246772740,737605486]]
private def rkmC_w64_s5_12 : List ℤ := pzigCat
  [
   [537180584,386392822,365634611,1301673069,1277710497,80673018,2024133086,3409484476,
    2827931290,382082437,5078060901,7912027807,5905316659,1569307678,11314031172,17314524644,
    13646375624,1353469953,22332946333,36781349577,32502447259,4598162381,38618860646,
    75467892094,79747768474,34813677272,52013532629,144623754541,189519974053,140294348039,
    12775924908,225033865178,400999112478,428557944218,232483927814,173031566499,660458447763,
    1013914031121,1003330888463,489736802017,479932176036,1631534994092,2511268058826,
    2622142527550,1619346241364,501498402465,3297403485439,5911179915975,7263917019113,
    6376518075541,2738389406729,3392374129456,10858666893374,17718414552150,21610700674024,
    20311730319876,12359712282474,2397569909475,22477566238451,44754081244967,64792634215461,
    77481427478941,77842700650543,61870218045091,27240508888689,26235984693292,96494427400504,
    179437132699362,269446156699712,360087066568400,444882896792564,518040198648024,
    575024274530356,612924689768764,630586312073198,628521148176360,608648784367640,
    573921274304902,527903788360956,474365223479336,416926731609998,358795578957278,
    302595134056918,250287674364582,203176247265726,161964358205664,126855099584840,
    97665551215078,73943511562248,55074252780908,40367438629160,29126040693406,20692722924008,
    14479277965724,9980825412398,6778597593568,4536747907236,2992260773102,1944999073750,
    1245901744852,786241042392,488825358328,299105853992,180076029020,106411140456,61639571330,
    34663620272,18903176106,9781678486,4527575832,1809994050,402825770]]
private theorem rkmWC_w64_s5_0 : bWinChk 564 22 100000000 1024 rkmPhb_w64_s5
    580 rkmXsWin_w64_s5_in 610 rkmC_w64_s5_1 4255044814 = true := by decide +kernel
private theorem rkmWC_w64_s5_1 : bWinChk 564 22 100000000 1024 rkmPhb_w64_s5
    610 rkmC_w64_s5_1 635 rkmC_w64_s5_2 4005375281 = true := by decide +kernel
private theorem rkmWC_w64_s5_2 : bWinChk 564 21 100000000 1024 rkmPhb_w64_s5
    635 rkmC_w64_s5_2 659 rkmC_w64_s5_3 3964983455 = true := by decide +kernel
private theorem rkmWC_w64_s5_3 : bWinChk 564 21 100000000 1024 rkmPhb_w64_s5
    659 rkmC_w64_s5_3 684 rkmC_w64_s5_4 3806040252 = true := by decide +kernel
private theorem rkmWC_w64_s5_4 : bWinChk 564 21 100000000 1024 rkmPhb_w64_s5
    684 rkmC_w64_s5_4 706 rkmC_w64_s5_5 3999477543 = true := by decide +kernel
private theorem rkmWC_w64_s5_5 : bWinChk 564 21 100000000 1024 rkmPhb_w64_s5
    706 rkmC_w64_s5_5 726 rkmC_w64_s5_6 3857908638 = true := by decide +kernel
private theorem rkmWC_w64_s5_6 : bWinChk 564 21 100000000 1024 rkmPhb_w64_s5
    726 rkmC_w64_s5_6 746 rkmC_w64_s5_7 3809188036 = true := by decide +kernel
private theorem rkmWC_w64_s5_7 : bWinChk 564 21 100000000 1024 rkmPhb_w64_s5
    746 rkmC_w64_s5_7 768 rkmC_w64_s5_8 2858246931 = true := by decide +kernel
private theorem rkmWC_w64_s5_8 : bWinChk 564 21 100000000 1024 rkmPhb_w64_s5
    768 rkmC_w64_s5_8 786 rkmC_w64_s5_9 3471055351 = true := by decide +kernel
private theorem rkmWC_w64_s5_9 : bWinChk 564 20 100000000 1024 rkmPhb_w64_s5
    786 rkmC_w64_s5_9 800 rkmC_w64_s5_10 3291509954 = true := by decide +kernel
private theorem rkmWC_w64_s5_10 : bWinChk 564 20 100000000 1024 rkmPhb_w64_s5
    800 rkmC_w64_s5_10 816 rkmC_w64_s5_11 3462711768 = true := by decide +kernel
private theorem rkmWC_w64_s5_11 : bWinChk 564 20 100000000 1024 rkmPhb_w64_s5
    816 rkmC_w64_s5_11 830 rkmC_w64_s5_12 3149192523 = true := by decide +kernel
private theorem rkmWC_w64_s5_12 : bWinChk 564 20 100000000 1024 rkmPhb_w64_s5
    830 rkmC_w64_s5_12 844 rkmXsWin_w64_s5_out 3567545404 = true := by decide +kernel
private theorem rkmWinIter_w64_s5 :
    RkmWinIterSound 271 1024 rkmHbWin_w64_s5 580 rkmXsWin_w64_s5_in
      844 rkmXsWin_w64_s5_out 47498279950 :=
  rkmChS 271 47498279950 (rkmChS 251 43930734546 (rkmChS 231 40781542023 (rkmChS 211
    37318830255 (rkmChS 191 34027320301 (rkmChS 170 30556264950 (rkmChS 149 27698018019 (rkmChS
    128 23888829983 (rkmChS 107 20030921345 (rkmChS 86 16031443802 (rkmChS 65 12225403550
    (rkmChS 44 8260420095 (bWinChk_sound rkmHhb_w64_s5 rkmWC_w64_s5_0) rkmHhb_w64_s5
    rkmWC_w64_s5_1 rfl rfl) rkmHhb_w64_s5 rkmWC_w64_s5_2 rfl rfl) rkmHhb_w64_s5 rkmWC_w64_s5_3
    rfl rfl) rkmHhb_w64_s5 rkmWC_w64_s5_4 rfl rfl) rkmHhb_w64_s5 rkmWC_w64_s5_5 rfl rfl)
    rkmHhb_w64_s5 rkmWC_w64_s5_6 rfl rfl) rkmHhb_w64_s5 rkmWC_w64_s5_7 rfl rfl) rkmHhb_w64_s5
    rkmWC_w64_s5_8 rfl rfl) rkmHhb_w64_s5 rkmWC_w64_s5_9 rfl rfl) rkmHhb_w64_s5 rkmWC_w64_s5_10
    rfl rfl) rkmHhb_w64_s5 rkmWC_w64_s5_11 rfl rfl) rkmHhb_w64_s5 rkmWC_w64_s5_12 rfl rfl
/-- Certified `w64` seg `5` (`271` steps). -/
theorem rkmWinSegWalkSnd_w64_s5 :
    RkmWinSegWalkSound 271 ⟨1024, rkmHbWin_w64_s5, 580, rkmXsWin_w64_s5_in,
      844, rkmXsWin_w64_s5_out, 47498279950⟩ :=
  @rkmSegWalk_mk 271 1024 580 844 47498279950
    rkmHbWin_w64_s5 rkmXsWin_w64_s5_in rkmXsWin_w64_s5_out
    (rkmw_buildHbFrom_length 1856 1024 19586394833 1024 0)
    (bAllT_hd (bAllT_tl (bAllT_tl rkmStatOk_hiw64t11)))
    rkmWinIter_w64_s5
private def rkmC_w64_s6a_1 : List ℤ := pzigCat
  [
   [251305465,867437072,1921361365,3756268462,7387615555,13785158000,22927369055,36313913738,
    54101387703,72363151504,90315605207,106799826130,116406393703,129119714542,146376068853,
    149079766496,125948860687,43922065324,102714369274,213889062717,209746039126,74149176903,
    99699226623,78473268460,84705159652,69356062287,181367833587,471311043856,394111731203,
    23230612797,70030330118,158025749556,352922449615,828019887266,1151165512969,1306230558050,
    1496035997297,1097259094816,856148640229,1349985344882,2332654956671,3724666121206,
    3802409508275,745312636582,2942313807340,3164972128315,4516160228884,1258351659443,
    4816094866889,2590465981648,1146498067908,1406684980468,3766860052563,1233004935886,
    1414767691544,1700284693329,9980973554370,4489168902050,13521915196183,1862880342767,
    18020050960260,11146276628404,1088983179815,378660624798,174114876922,2104632923319,
    12555989072398,35999124408614,35649372273474,4819468980730,22803240928917,12969933220249,
    32104803571342,79570756331112,98089496293044,80667156703688,43917678086094,13332332496230,
    9299028206474,40914839008090,106615402573304,197806540483212,302618349082170,408691683424182,
    504976384890764,582819834446838,636540271255966,663577283649532,664268009334684,
    641329386800038,599150607190630,543024326883110,478426520387518,410433694373102,
    343318173262112,280333852136208,223667081656104,174517776477218,133260517564714,
    99646341325048,73005789322654,52432512661194,36929569587130,25517675199044,17303582735182,
    11518111091524,7527805378064,4831496137122,3045485647106,1885366252428,1146297766342,
    684170976698,400971102578,230423218492,129607501934,71126424936,37713164340,19269440496,
    9062253446,3745411484,1117253840]]
private def rkmC_w64_s6a_2 : List ℤ := pzigCat
  [
   [332626789,1120557212,2454096713,4526274580,7666173493,12323195290,19011562775,28204106134,
    40167024001,54755737646,71239630347,88257309830,103973145183,116386818502,123600081027,
    123804853112,114931602453,94257188920,58669935351,6498693686,58650772940,123448775323,
    164073727040,154330576075,82750292410,31363964734,139198204757,190007194398,172810930487,
    136884691006,156717441757,255404275318,364258440245,387219433056,331018664745,359021108596,
    653022792273,1171467893624,1607423536009,1685701636364,1474916573007,1323829959696,
    1469650592293,1772851007800,1943511182693,1862001291480,1396285404087,254917787804,
    1535846538694,3193022987707,3482316648944,1753568640345,1239352528669,3815934877184,
    4364691914043,2443662816786,265545440180,1610203661565,1332236842284,435223594133,
    212158603672,1084164783965,1332216826502,370465227868,3046736134211,3701249588360,
    845770337972,6221219900747,3381014211278,4406386125936,5553695495393,326039955644,
    4167427231312,5676322783147,1221558585553,9778270581904,664858844823,11014275075147,
    1874789803092,11218412433852,853345582899,9660979079927,1946329462343,4427187908356,
    2192785665778,2472310398522,4086666417380,3220190776497,11004155502733,1409986036375,
    18946596675354,22088334985300,1291108142339,24938843805987,18365812574429,15788490988496,
    44312681738276,39264159125940,5246609402854,27139738940385,29567032965437,2269591426574,
    48802466791990,83011718748052,87874988671700,64075721787006,26829829004160,2970840775761,
    7396488140137,23401668845576,90003279542304,185284969142522,297262747286274,412111495279594,
    516737316324614,600632235649604,656937392270224,682760492620146,678870896504956,
    648948893249332,598597033842148,534306295283326,462541709144766,389046482849100,
    318409370550036,253887060277806,197431612179196,149864576629558,111126254996190,
    80547742019404,57102501681010,39612382007718,26900974392736,17890357750916,11655040477964,
    7439668333884,4653713049632,2853206693606,1714458768522,1009667659426],
   [582523503226,328983064194,181705364846,97831715572,50978254490,25486163476,12062139044,
    4930165608,1615877322,276002874]]
private def rkmC_w64_s6a_3 : List ℤ := pzigCat
  [
   [558697580,1789697703,3659117940,6243225991,9780715000,14625710299,21164212520,29720196561,
    40455634436,53263669111,67664883806,82733168451,97086691544,108970125191,116424504610,
    117503607289,110478524674,94005997065,67326853102,30659128699,14051418815,62075532118,
    105031215437,131162702030,127819141793,86443597280,8690700777,89715984305,181575030196,
    239267301351,250793738744,231168488899,218377517872,251407919227,343014838872,470095561673,
    596192462806,712968765243,861117266594,1096701407571,1416869127152,1714887505477,
    1834436224140,1706759279059,1445574353194,1271021941241,1288011541530,1326066330149,
    1039995454150,224108145027,952215961663,2020792594378,2501571270931,2102757319492,
    756685846733,1293932751019,3315779447730,4200925728661,3172221841988,604836678513,
    1985802416647,3051284061756,2222664928813,464854568086,824544300860,918576125733,
    292362885974,70881174353,696072254104,1249520362089,452122681160,1541815754074,2758744555433,
    1401548759384,1901134196616,4077699794167,2143499600028,2883632938538,5336365721505,
    1392902923636,4800319354432,5291352027227,1234011529129,6274063087586,2746570268387,
    4111683009163,5156153365452,119744332224,5659262833679,4072659392686,5045194781378,
    7284670343217,4316963860159,8900162442266,4076838828622,8616298117149,4074954530317,
    6661639997262,3503169953424,4116228604011,2268935742651,1510556787290,36593751326,
    861480459798,5058578785388,1198095551070,9570474518781,8906086015603,7690757440640,
    17675904197846,3268245718472,19303842938705,19140567546229,7460640892106,30209986655720,
    21461476379848,10838136790005,32269594412199,19349100724459,17159815180638,44496344393250,
    39103839462648,6014225537588,27771554129201,35762175719565,10470515727241,33971992525442,
    73094106491472,87154318581976,70777487426824,33794736630006,4614255395547,24090273888777,
    9846536759733,43808414144408,133216546281768,247450526599516,371541699588630,489836839249640,
    588792712241554],
   [658830178727878,695149983197490,697608414004964,669890486259536,618281926398256,
    550331900207864,473651853131818,395000945716934,319725588075918,251537562813766,
    192565478701240,143591248465098,104378315483736,74016914248336,51233038279732,34633010436582,
    22873414695464,14764928561006,9317845534918,5749931808276,3470138288602,2048322819666,
    1182339254666,667181847050,367823960214,197776509450,103365372694,52242193204,25279079506,
    11391164772,4422119436,1160232950]]
private def rkmC_w64_s6a_4 : List ℤ := pzigCat
  [
   [388857635,1316653016,3085418713,5978152620,9682729145,13942674730,19534894953,26637924086,
    35550437943,46269604552,58541010885,71796690588,85130103563,97295674750,106763833069,
    111844425786,110873947923,102446564782,85665744325,60405131458,27585644725,10521533459,
    49998112320,85120571329,108603828918,112580094797,90525391424,39937647687,35074264579,
    122726213134,205520682315,265832591236,293828084435,294288415550,287952478181,304622466418,
    369683399125,490855468942,654097725499,833343766228,1008894205957,1180185814764,
    1359247553911,1545311893682,1700772619547,1756152877384,1653270098659,1398815875824,
    1076417746253,786480538656,547794702733,251834655512,256443085634,1001770611995,
    1749095590228,2067979750091,1592671932264,299873030917,1411169998319,2893607601764,
    3542099698325,3020979529106,1389380972761,834736256979,2734707219454,3349282330981,
    2292370963290,186958789383,1630815925275,2088326302854,1214215077881,13412595538,
    518502433830,266414455063,67212926977,188326680771,903468615432,1189401399719,277901861904,
    1459625507404,2433613565127,1235748227328,1569723674800,3410903793573,2086283903358,
    1644551917188,4206829095873,2570059057060,2153732238552,5014220612265,2301838776146,
    3486013558224,5456932370841,654779811476,5188058922032,4443375747641,2058835918681,
    5797275077410,1870706455273,4449259757575,4717249898998,1385843752354,5681670077305,
    2143021516790,5047803873090,5219050466579,3674778986327,7339861962176,2404167128164,
    8287431191167,1678992378475,8037597989212,1485163808770,6701771882725,1462154530951,
    4517836375680,1026843542418,1985766950273,333137581878,103460945551,2684472786543,
    1061970288562,5929788499274,50605796633,9773737543859,4847179360909,11237563502920,
    13622844993976,5192815616941,19963447188301,7793799392897,17391615877342,21936652728228,
    2399001824235,26607710392599,20392067358473,11003986518252,33176377010670,21618890958020,
    12325693708691],
   [34585678133671,22903215480059,13073884807936,42572938352974,41376399826074,10787582237174,
    25524384104483,40495196290633,22196025474207,20152140602150,63775960794500,86273948568678,
    77068750612972,41380533589358,3256328904049,34656898703317,33919105755961,9126102315912,
    93987165278480,210747518708576,343354742697246,473673878737530,585217188613194,
    665835642660352,709067742980296,714188918949286,685260014205974,629587390717398,
    556018803366180,473417046537472,389522702830696,310290405636974,239669154488120,
    179725195446194,130981790189236,92853064001372,64073985183916,43065628796962,28207310746016,
    18011669078688,11216270531246,6813145378774,4037577573554,2334510028260,1316780319948,
    724222300368,388063381250,202299821018,102294101506,49798394254,22935881544,9633789336,
    3408742482,808433598]]
private def rkmC_w64_s6a_5 : List ℤ := pzigCat
  [
   [565698999,1761100064,3649106303,6475185264,10293453519,14873106476,20317519475,27194257366,
    35506557191,44893796968,55716842941,67605096662,79942245571,91410182366,100579942919,
    106218715580,107164546455,102063262950,89747355155,69957585220,43419570825,11552242428,
    23123042820,56526402263,83622068242,98981146571,96985925814,73367812937,26973213340,
    39512145080,118478427407,198211495450,266120258407,312269765476,334800646973,342246731208,
    353192554777,390611659966,473325218845,607509166350,783038608577,977269375292,1165007319079,
    1328896528632,1462993453259,1565971607362,1628221457669,1623908789866,1518361520073,
    1290515158158,955420765057,565496335818,181266399153,170958465901,515956685574,891191591789,
    1266703479548,1487056216619,1308886251938,550220503201,728042075053,2145858521722,
    3125571548607,3170791789284,2140125945135,346946586258,1565502665096,2886469060269,
    3107045614934,2118703614399,306183059210,1530049729590,2498863693307,2124157503842,
    716327641955,765875014935,1392489956796,975958001213,165061507244,217171162636,27236677900,
    335037278037,51832201404,782657714136,1355459599705,836288228850,707561741354,2109984678709,
    1958065916730,51960068658,2453426030087,2979581633400,706887680829,2605488213563,
    3753022303256,1227002324481,2830147222777,4314805732960,1326927544453,3367242853991,
    4693377908154,765441974485,4331815374065,4581201460664,713855560304,5329948326027,
    3404101362954,2842138089264,5464447802213,1055038871290,4632736344654,4200580120577,
    1726894737427,5342676283018,1748247600957,4408062161221,4535485984550,2094198189726,
    6068465658439,685562501688,6429680652448,3161973252351,6046920000599,4833796982572,
    5351938645616,5469424724039,4564346428101,5092576888640,3666547261938,3946906872079,
    2510006343583,2423103111026,928920102802,995089295281,1175947178256,211696923266,
    3705707199797,632095392873,6251525898554,2673083281070],
   [8117417067725,6588721125693,8138028018156,12229295693874,4219074320291,17474815053329,
    5234180013539,17213775614284,17216589116138,7567283631157,24128522384237,9005764682885,
    19629075690392,25274481426018,520961648947,27882401558573,24634689664109,6737134761056,
    32874756096932,26256547527006,6827825439575,34178817950041,29606954438061,3690478544218,
    37846076841666,45140117444804,19890743194608,18911109186995,42960858289651,34330682561753,
    4057986466440,51855880829740,84000391436848,84142491728866,52035336963860,2776456690610,
    40050330882135,53370610478325,22100753677299,56994203722886,175430729601280,316207879509424,
    458565248063364,582775115516470,673830717324474,723449602865196,730344950574824,
    699116300857888,638323419711080,558330175892358,469390337727584,380263751698722,
    297459249364786,225046981053228,164892349858304,117133991922968,80743876456078,
    54050470905550,35156956732158,22230613478730,13670419056514,8177521879728,4759256807498,
    2694862172666,1484364011170,795061364800,413728322046,208879112806,101654371682,47417929940,
    20877513236,8290261278,2713444980,585130078]]
private def rkmC_w64_s6a_6 : List ℤ := pzigCat
  [
   [206476581,895211058,2628521029,4950796072,7982160537,11970037678,16916319791,22698769736,
    29469391795,37542609964,46817546367,56867924668,67601732807,78764988062,89095284523,
    97345610130,102641407677,103516831712,98926655049,87853360290,70351084923,47059454732,
    18952606699,12178438019,42991444270,69170060067,86387554834,90347395063,77190407214,
    44767538653,6638149143,73521542764,148752912473,223356206042,288153762783,336010605778,
    365746757611,383596848340,403373999963,442670169676,518028958231,638455179372,800586054141,
    988401861412,1177977275503,1344725597354,1470572250945,1547005629642,1571218764081,
    1538840519640,1439036064177,1256303583632,981294606331,624235056022,219752949617,
    182062421339,536080443954,818407199977,1021008105644,1124079801435,1064780696258,
    740520216187,67796867122,919726755676,1998131636659,2778033443906,2854740470407,
    2025615035172,451099131111,1354289091847,2721832568810,3123324946075,2406750964172,
    859945555163,910161690471,2214073442396,2543934947199,1789583898788,325943991513,
    1114993780837,1804337873518,1453066054053,421820559576,522424297164,787087418215,
    413242188320,16785201124,20723465110,441363185719,620971783780,65685202673,965006887681,
    1550798417490,924518473725,705286162159,2119757544206,2001624896507,128115926014,
    2176449267990,2912007843599,1126923157164,1932889335614,3560612677027,1980213265480,
    1677899968088,4019779599703,2538071536238,1631427814090,4408109087725,2743297283040,
    1950735761520,4798698370263,2488897084944,2748624239530,5067217496241,1550993045644,
    3918675632932,4794835868641,159841316709,4943258291842,3572659212931,2259912181443,
    5162539274286,1453104276915,4078368043089,4274329819910,1178951178826,5147335172173,
    2130526793964,4072701628624,4686783142461,1741814443607,5943697008578,968104351179,
    5951128500917,3350043953656,5119461777026,4991535453031,3947892261163,5735648304834],
   [2817224199264,5593494310791,1886023174429,4685039856780,1097612092618,3218586127395,
    266525426559,1471239688364,817431300283,244052969928,2326892853588,1584945593577,
    4360218822251,2150095343120,6865341447786,1472765119301,9525299623403,903818684265,
    11663202217158,5305282154132,12072818627845,11571108521225,8868433976302,18034156269764,
    382670236227,20636906145731,12117772741593,14908283720466,22843944339030,496973437109,
    24696925639983,17428708462001,13214378648624,29332933767242,10488609552330,22108234317271,
    31276982779277,6176036993683,26859536129600,33545515208664,6819533491912,27595992491291,
    37175895507669,12436333247519,26182021957762,47171028498300,33745597669266,4317904170725,
    39395328721155,46033746500381,17275457782779,32255907853928,76084867727510,90904041888126,
    68288040642912,18136303610960,36152472257383,67262476614587,53773230631081,13289286722340,
    128666790559784,275445574834030,430370563662642,569882108827260,675157819665006,
    735130889480840,747229993382708,716213016742480,651826114879286,566093841059118,
    470900720021854,376265405261692,289436005265346,214720313141712,153840860620040,
    106572113865942,71447188804722,46388972246766,29186262258920,17801994241450,10529657684374,
    6040546366182,3361072054292,1813754175120,948638940846,480545829592,235150113870,
    110757231492,49734642214,21068411138,7987773806,2470027826,318571792]]
private def rkmC_w64_s6a_7 : List ℤ := pzigCat
  [
   [683114865,2016294886,3951082653,6710348628,10343751013,14647300486,19744814401,26006227742,
    33186522709,41057761470,50109983899,59893649512,70003264127,79874853162,88928028655,
    96077030976,100009133539,99807395762,94673827385,83632624114,66558798049,44417370310,
    18217294269,10343657029,38312824096,62291324267,78424008192,83327194659,73359229388,
    46180379293,1916860434,56968305298,126096957967,199000057940,268133103581,326585918112,
    370332116779,400901169234,425429281587,455648214014,506242865541,589849829404,712844308641,
    871421668706,1051365868737,1230463897386,1384564713385,1493539943260,1544914175913,
    1534501474294,1462889692789,1329696868750,1131555333707,865202719132,534345722917,
    157688452420,228889521458,578612050991,846355574098,999795558365,1019065706866,887476649163,
    580684288178,72845310131,630832966125,1445384743812,2176315294023,2547128362216,
    2300627570691,1342549104018,149225889402,1729331753925,2833059001536,3016695314111,
    2171880690132,597914919389,1111868590061,2316845881496,2589301511249,1876552824320,
    510754432533,926489796109,1835363139210,1855129961691,1044997231148,121207104426,
    999010388809,1156937017868,655743299277,11367617565,318843388076,147176668613,131867776749,
    39503749338,484140780268,931998389751,673196899044,373098998856,1487688230979,1657512430908,
    478044266789,1337242395385,2371540397002,1616441194753,581058234787,2579393817438,
    2639115871033,436139859236,2390467976222,3380253437795,1400264105634,2050323017456,
    3863655944313,2132247754656,1782348252080,4194334101987,2567142643152,1742864651590,
    4479737969475,2676329257730,2041516221702,4760212267289,2377321085368,2734663312476,
    4919970300913,1523661685534,3714124485846,4658142551249,68643820192,4610533605956,
    3683088595341,1737730367347,4958037228324,1978520138545,3457729557097,4477869556252,
    268257580700,4723814322811,2970695667888,2908602555414],
   [4983507484763,4524773950,5282994734604,2917126220335,4101779018061,5047930170670,
    2068909577288,6088343575659,126263371804,6123132937196,1946968521479,5445461163353,
    3083615167946,4373962200550,3440211261253,3131673957657,3087106826766,1809289258994,
    2213857193851,395588768333,1082435040994,1162672111959,21754005624,2911350438554,
    822259055339,4867139322067,1049332499420,6991176793384,413378570139,9120167888123,
    1387843492769,10873299437946,4584118673464,11573603402939,9162207087333,10210916342076,
    14543976052844,5570166316801,19040973930833,3011869276571,19613642566516,14063242952358,
    13207942483443,23020406008377,280939746903,24141964548556,16402036900166,14098883500909,
    27556108256915,5883984729923,24688150494530,26826615641888,2867328783445,30826445028761,
    25620674318757,7689141520762,34378070415084,27014291341372,7615142023507,36636734395155,
    32768655975065,1689824845414,38358066160746,47409746204018,21067351329174,21673793333803,
    49907579688147,42311209123689,364096328187,53584199345082,90004693909926,88432974643342,
    47647964283782,14056773887385,67017182556059,82015785652777,40619848491735,59401116938970,
    204504505115472,370414371371104,529360747946180,657009690971622,737268456797430,
    764196585483116,741230167347926,678578191678310,589871538494232,489025752885250,
    387931820220728,295208260031258,215927650940568,152043327965224,103189097951198,
    67565258932334,42712264190934,26082993559008,15392048132432,8779446875872,4840375826256,
    2579247651330,1327620790926,659536207938,315520532022,144972992410,63462922098,26088319576,
    9770277770,2928443260,347146618]]
private def rkmC_w64_s6a_8 : List ℤ := pzigCat
  [
   [506782629,1553022020,3303996891,5940775036,9174743165,12983242176,17918139149,23524590396,
    29909188933,37257470248,45518488607,54351945958,63609360533,73121499916,82094657371,
    89663942812,95312332799,97862867286,96044957859,89539984402,77777155459,60680238798,
    38715588737,13542708742,12970420762,38584839015,60009571166,73784415125,77021880660,
    66833496767,41205511196,53995124,55209961881,120409887892,190817153045,259913232628,
    321581615805,372148677166,411304688809,442466700398,473683492175,516523508310,583026204925,
    681767121220,814248032619,973742801800,1145073674529,1306616744388,1435760217753,
    1513358591676,1528178456129,1477139268792,1362771491177,1189514412018,961462205161,
    681948386514,357787877071,5200919356,347136490488,659032441597,886281752530,991201366227,
    949562039642,752022257467,400378034698,93016010466,698035179341,1347278959054,1917491649649,
    2233377791626,2111170632671,1440279652342,273233195293,1129330621091,2344096081614,
    2927983585811,2608862465704,1432660695825,215746742501,1747066272776,2605107011659,
    2496328085856,1507058511725,57495235414,1277234173464,1997905712463,1871404305666,
    1016131088145,149765512745,1088800603108,1394573082805,1001037175714,221285345055,
    443854271223,634631151872,376245388471,33700930362,18847312922,247089068114,462122425589,
    205486037266,527914484074,1191059360905,1086585336446,24798464017,1352152221485,
    1954864380566,1119124620541,735823230477,2273189053668,2208465971057,381099097318,
    1947649142274,2931957592577,1598701782820,1195695813482,3224568238197,2639255154814,
    315313453236,3214671919021,3400339782324,460772250593,3089457865029,3904691358586,
    1002997783571,3014206083395,4225580263598,1249342592437,3110787969587,4419452505186,
    1147993965283,3446094919241,4461807647068,628099093939,3989148636219,4214746308386,
    346429227240,4552135107749,3489797423734,1663573334902],
   [4826645775521,2209454059790,3040681399274,4553025106229,476261731614,4176780778414,
    3599297186703,1570289563889,4800601854490,1775603028561,3755444807463,4348774087126,
    1161278266498,5287930499577,1852848537022,4538960427218,4296518842065,2625545412659,
    5628132935200,286406927632,5785848677185,1824537741278,5039659278248,3288291226341,
    3792086043723,3935620248932,2413729700732,3787185346511,1146483600883,2974826903574,
    78134137014,1682190105677,831523661486,110053867850,1698396814509,1544893824824,
    2660865864746,3101579621113,3850234274447,4392601539266,5381850803342,5235061510337,
    7340818133319,5381076158148,9730010848254,4486906785399,12371268724817,2141985577168,
    14785011910888,2013650386038,16065992595837,8022663754263,14839645873348,15104443873572,
    9593529287227,21076391856523,224728416397,22511449876640,12714175127620,16445965173605,
    23208455577455,2800200575826,26101212306204,14589947171420,17253634015301,28095206264915,
    3346040082199,27068714813786,26270763284000,5559227467765,32479418439943,24309978967875,
    10674919121688,35974782696250,25428105585308,11234338636537,39233952645147,32025213478853,
    5366149728970,42014595629800,47697284582762,16768558841312,28511012067317,55031812356559,
    41906101297001,6336090818484,63304126692928,96743308115300,86489019790248,34844109765020,
    34565686526077,87260233327927,91860739580307,31445497491875,91495051251268,257140162207254,
    435479655355742,595291589366748,711893027518002,771714966406764,773184823029306,
    724592216682796,640260971914484,536432539789232,427908417288634,325986611297450,
    237726921431924,166252341717832,111651946422190,72082350783608,44770201881448,26765783578224,
    15407761661784,8541387742592,4559380317904,2342599374038,1157688832150,549478017800,
    249779859310,108266528978,44418703656,16581825436,5303771776,1194518666]]
private def rkmC_w64_s6a_9 : List ℤ := pzigCat
  [
   [506886589,1527268530,3206463029,5728486444,8845306547,12546783494,17267562701,22541354940,
    28564606241,35504594108,43201046045,51406975780,60143237095,69097441950,77539580733,
    85157217530,91302557279,94667521542,94797350191,90904943198,82248183761,68509033780,
    50331502865,28385346604,3821342243,20962483375,43507215904,61277974991,71048035868,
    70081206371,56180099804,28403809133,13643378427,68340841570,132026699951,200254651988,
    267983817897,329913780758,382593344135,425486216932,461357135247,496292685066,539122336761,
    600224874034,687354940121,803880179758,946629864387,1104673005390,1260178015109,
    1391899341254,1479877044169,1509420983272,1472457085455,1368666532326,1204234176173,
    987648278542,727662103441,432591848048,113551692355,211876519869,516942474384,766757126189,
    922813980788,951560060657,832503841578,562989455729,159402264568,345029949954,899675907855,
    1431738026688,1842765013417,2012809275380,1825175736399,1213103236236,215832681973,
    985015383495,2078621351508,2707290921419,2599762469326,1703067258431,247645198116,
    1302655334940,2412320757575,2686374292412,2037393932269,726749772632,739942427296,
    1819289167539,2143821850872,1654968710589,607352952836,547042651170,1345055736189,
    1498917112132,1013689210213,180126650354,568643057544,883338245843,691608743406,228589896181,
    137206733059,179896193564,9767153808,111592400107,118317078733,570686519674,807457269353,
    426428774248,509067607566,1377756490347,1414325875124,360526142995,1186993847565,
    2100757470500,1558844273397,233789868217,2055269261542,2500041497715,1070402942944,
    1314854663738,2874624602761,2285367961432,186598202370,2697518022615,3161195687914,
    996131022233,2171493203119,3659936329110,2010902258665,1533565644727,3875314422406,
    2767298602801,969845440553,3947404977628,3267010424499,599090939663,4006449704984,
    3543038969673,496738602499,4141649435684],
   [3604445540465,716268061329,4370840621230,3402847282527,1278186449773,4612738403568,
    2849772277089,2122558266017,4695141208574,1890924015635,3081296099113,4433955319966,
    573842250753,3937173587149,3718990824962,991533466646,4505021760243,2465067070110,
    2713970082126,4538377117905,494904227006,4356359112128,3499305050689,2236697642141,
    5084064648994,764434470625,4854679265293,3490873305366,3164307979970,5156729346011,
    765748377181,5512158913080,1562224676615,4758947419883,3262573279104,3343565874864,
    4080511739757,1749488985807,4018183494380,356474775798,3233986641033,622141683598,
    1940925107500,1137550330379,338657270557,1267506797064,1416731138807,1164960937473,
    3217116161364,1009426669798,4994203169359,976768869433,6709041914998,1232222167760,
    8332693741645,1942619148181,9809171548374,3284956155670,10997612761231,5425125741265,
    11612246437980,8447729078390,11187684775335,12233892830695,9099282536780,16286648299786,
    4697128805259,19525212962029,2328878072905,20218601530354,11305461690432,16427300781035,
    19985471498507,7178875759312,24792037669106,6206049403024,22275550622935,19782675284783,
    10929844885550,27809449930550,7420371236338,24028092374067,25756917939097,5280428459120,
    31411078308884,20925569835604,14611158291071,34933742650129,17043911567531,20344750225094,
    38029169204550,17250108448258,22370451072181,43023502675127,24448509251953,18510383678876,
    49849202988014,42916936485850,1369028191928,44373283730817,59841752737817,30474540560499,
    29134598565150,84777869995570,103127667912976,70466276812012,57962709246,74022834907175,
    111957165382173,84357098642289,17210001235210,178498307290242,368776284244888,
    551353262369622,694137605584848,776929972723654,794022703230608,752514227730582,
    667914466729178,558956985115188,443169414694128,334055839120802,240026600709276,
    164716776903160,108114175581036,67943246461790,40910800030884,23612519227666,13065536958942,
    6930133766048,3522301256902,1713796009750,797199488516,353798634862,149051540938,58981713442,
    21443454742,6888467062,1483735332]]
private theorem rkmWC_w64_s6a_0 : bWinChk 709 21 100000000 1024 rkmPhb_w64_s6a
    844 rkmXsWin_w64_s6a_in 847 rkmC_w64_s6a_1 2849220051 = true := by decide +kernel
private theorem rkmWC_w64_s6a_1 : bWinChk 709 18 100000000 1024 rkmPhb_w64_s6a
    847 rkmC_w64_s6a_1 829 rkmC_w64_s6a_2 1363403975 = true := by decide +kernel
private theorem rkmWC_w64_s6a_2 : bWinChk 709 15 100000000 1024 rkmPhb_w64_s6a
    829 rkmC_w64_s6a_2 814 rkmC_w64_s6a_3 1648660336 = true := by decide +kernel
private theorem rkmWC_w64_s6a_3 : bWinChk 709 14 100000000 1024 rkmPhb_w64_s6a
    814 rkmC_w64_s6a_3 799 rkmC_w64_s6a_4 1765030105 = true := by decide +kernel
private theorem rkmWC_w64_s6a_4 : bWinChk 709 13 100000000 1024 rkmPhb_w64_s6a
    799 rkmC_w64_s6a_4 785 rkmC_w64_s6a_5 1427471755 = true := by decide +kernel
private theorem rkmWC_w64_s6a_5 : bWinChk 709 12 100000000 1024 rkmPhb_w64_s6a
    785 rkmC_w64_s6a_5 771 rkmC_w64_s6a_6 1428685946 = true := by decide +kernel
private theorem rkmWC_w64_s6a_6 : bWinChk 709 11 100000000 1024 rkmPhb_w64_s6a
    771 rkmC_w64_s6a_6 759 rkmC_w64_s6a_7 1256014556 = true := by decide +kernel
private theorem rkmWC_w64_s6a_7 : bWinChk 709 10 100000000 1024 rkmPhb_w64_s6a
    759 rkmC_w64_s6a_7 747 rkmC_w64_s6a_8 1096597340 = true := by decide +kernel
private theorem rkmWC_w64_s6a_8 : bWinChk 709 10 100000000 1024 rkmPhb_w64_s6a
    747 rkmC_w64_s6a_8 735 rkmC_w64_s6a_9 1063824851 = true := by decide +kernel
private theorem rkmWC_w64_s6a_9 : bWinChk 709 9 100000000 1024 rkmPhb_w64_s6a
    735 rkmC_w64_s6a_9 724 rkmXsWin_w64_s6a_out 912312185 = true := by decide +kernel
/-- Certified `w64_s6a` partial walk (`133` substeps). -/
theorem rkmWinIterSnd_w64_s6a :
    RkmWinIterSound 133 1024 rkmHbWin_w64_s6a 844 rkmXsWin_w64_s6a_in
      724 rkmXsWin_w64_s6a_out 14811221100 :=
  rkmChS 133 14811221100 (rkmChS 124 13898908915 (rkmChS 114 12835084064 (rkmChS 104
    11738486724 (rkmChS 93 10482472168 (rkmChS 81 9053786222 (rkmChS 68 7626314467 (rkmChS 54
    5861284362 (rkmChS 39 4212624026 (bWinChk_sound rkmHhb_w64_s6a rkmWC_w64_s6a_0)
    rkmHhb_w64_s6a rkmWC_w64_s6a_1 rfl rfl) rkmHhb_w64_s6a rkmWC_w64_s6a_2 rfl rfl)
    rkmHhb_w64_s6a rkmWC_w64_s6a_3 rfl rfl) rkmHhb_w64_s6a rkmWC_w64_s6a_4 rfl rfl)
    rkmHhb_w64_s6a rkmWC_w64_s6a_5 rfl rfl) rkmHhb_w64_s6a rkmWC_w64_s6a_6 rfl rfl)
    rkmHhb_w64_s6a rkmWC_w64_s6a_7 rfl rfl) rkmHhb_w64_s6a rkmWC_w64_s6a_8 rfl rfl)
    rkmHhb_w64_s6a rkmWC_w64_s6a_9 rfl rfl
/-- Cumulative `w64` part `11` lane witness. -/
theorem laneWitness_FindAllJohnsonRampKickMuxHiW64T11 :
    @rkmWinIterSnd_w64_s6a = @rkmWinIterSnd_w64_s6a :=
  (And.intro (Eq.refl laneWitness_FindAllJohnsonRampKickMuxHiW64T10) rfl).right

end
end QuantumComputation.Specs.DickeSol
