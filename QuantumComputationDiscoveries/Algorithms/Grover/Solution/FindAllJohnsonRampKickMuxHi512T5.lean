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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi512T4

/-
# High-`m` Checkpointed Walk Part `5` (`FindAllJohnsonRampKickMuxHi512T5`)

Certifies `1` `T_16` checkpoint walk(s) (`64638` substep-coords).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section
/-- Zigzag `< 2 ^ 60` `ℕ → ℤ` list decoder (`FindAllJohnsonRampKickMuxHi512T5`). -/
def rkmZigHi512T5 : List ℕ → List ℤ
  | [] => []
  | w :: ws =>
    (match Nat.mod w 2 with
     | 0 => primOfNatForced (Nat.div w 2)
     | _ => primNegSuccForced (Nat.div w 2)) :: rkmZigHi512T5 ws
/-- Quantized generator list for `m512_r512_s1_c0`. -/
def rkmHbHi_m512_r512_s1_c0 : List ℤ := altBuildHbFrom 512 512 83534166666 0 512
/-- Input orbital vector for `m512_r512_s1_c0`. -/
def rkmViHi_m512_r512_s1_c0 : List ℤ := rkmZigHi512T5
  [14,12,1,2,24,6,10,14,20,14,24,38,36,54,66,134,294,762,1916,4840,11900,28572,66934,153117,342129,
   747405,1597357,3342400,6852020,13770646,27147030,52524456,99792107,186267195,341727442,616470955,
   1093982042,1910461597,3284383049,5560389625,9273283097,15239564583,24685940176,39426306473,
   62100827580,96492560502,147938345870,223850920028,334367908358,493139955030,718264153116,
   1033359652608,1468769486708,2062856181880,2863338891204,3928597375420,5328844469008,
   7147045599814,9479443914232,12435535450382,16137333669824,20717769500952,26318094429598,
   33084191831124,41161756190198,50690370060352,61796591754020,74586258157128,89136300359020,
   105486457253494,123631345403046,143513393748456,165017171517518,187965621015594,212118650511436,
   237174446020394,262773727869730,288507015548656,313924782784080,338550196851046,361893956109834,
   383470582165128,402815401237592,419501374262506,433154914285782,443469866000768,450218914158532,
   453261828894064,452550136481770,448128010283584,440129393382860,428771575787604,414345640176146,
   397204348116436,377748153826928,356410098980106,333640357994018,309891170902522,285602825950022,
   261191244997688,237037591962724,213480178973548,190808797682340,169261464166220,149023443293860,
   130228318387760,112960798149512,97260906450996,83129180907682,70532510547268,59410267469628,
   49680427458502,41245425032064,33997544505052,27823705844036,22609558710336,18242847243636,
   14616049898270,11628331932952,9186872683378,7207645867436,5615739714344,4345305819996,
   3339222621900,2548552604380,1931863062644,1454469606206,1087650511902,807869283598,596032868512,
   436804262384,317980883290,229944153664,165181145674,117875796074,83564917680,58852844112,
   41177860072,28623418146,19767374350,13562958608,9245828936,6262259730,4214225480,2817821180,
   1872084266,1235835976,810637634,528360132,342197930,220229396,140841344,89505198,56524370,
   35473036,22122891,13711082,8444876,5169057,3144352,1900884,1142052,681910,404646,238630,139850,
   81439,47123,27087,15458,8756,4916,2728,1494,800,414,204,92,36,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
/-- Output orbital vector for `m512_r512_s1_c0`. -/
def rkmVoHi_m512_r512_s1_c0 : List ℤ := rkmZigHi512T5
  [7866,53906,289598,1130514,4124978,12253086,34954246,85819068,202433052,425954792,855000350,
   1567827846,2718514006,4366072830,6571447646,9195772022,11928778444,14256922640,15467254732,
   14908200272,12140436412,7233107750,967805174,5290569549,9841622027,11219652465,8863359231,
   3445433829,3136861622,8334862344,10015125706,7398796938,1544109082,4920663067,8971179467,
   8645014441,4044869415,2545712398,7725825726,8776219576,5121858384,1279083981,6885275101,
   8546376855,5337647957,890876310,6515968414,8216671336,5003057322,1151343681,6507394431,
   7804690149,4267228607,1856346886,6700114962,7242599244,3194740056,2818109137,6909793705,
   6463550349,1846766613,3874239450,6957054540,5414733324,330844526,4864639789,6724357007,
   4080686073,1230375986,5618718634,6149374436,2532559880,2711352343,6021029477,5206650619,
   886117891,3957540720,6022979698,3960692152,744321239,4855579035,5601870745,2530055285,2210108802,
   5362545902,4818298548,1023201708,3397854741,5451011103,3784704955,414816266,4262616648,
   5173425584,2597555372,1676118389,4765332853,4623405883,1395386293,2710224410,4948768716,
   3880300596,271655768,3465634857,4876897659,3071554257,713599968,3974961122,4613186424,2269398658,
   1501948475,4264135873,4264727997,1548286703,2109883970,4384935238,3880856548,961459726,
   2523175773,4404912529,3544800675,519993971,2780461252,4353386458,3286292724,260738866,2890367153,
   4291185835,3141422217,164805387,2869281640,4210622028,3122039534,262018582,2719280071,4134649457,
   3218520439,528499155,2418210924,4011765322,3414640598,983453022,1949468225,3813398701,3647408149,
   1584027363,1270790200,3443716546,3845211314,2302082048,377849471,2839256789,3876945599,
   3020223067,720671513,1902706512,3606964790,3606369132,1928639446,623297551,2873958187,3822314051,
   3070037129,966306747,1563357510,3425876576,3834166114,2632204738,331616826,2127739939,3763745053,
   3929838799,2555751495,164708831,2341810544,4036809290,4304463972,3039104352,661986056,2030864209,
   4140163729,4965436079,4227301781,2134897937,702208126,3465468152,5361529426,5842349258,
   4751299222,2349445380,777097165,3881423667,6236037237,7292565395,6795878685,4827045293,
   1763313987,1824482686,5296115304,8056542620,9649592346,9823132240,8552098818,6013531166,
   2528937634,1500684009,5653461989,9539337883,12845289631,15362162619,16985267907,17695901275,
   17538203213,16596679707,14968758743,12729195277,9893006875,6384138095,2005798463,3599893130,
   11010835080,21101672518,35138594488,54902541244,82857045124,122371866848,178006096242,
   255855451468,363976307742,512901898544,716258602366,991479349840,1360606099902,1851172765162,
   2497154367506,3339952567194,4429367792850,5824492818726,7594453015678,9818908362098,
   12588217667376,16003151171088,20174032829740,25219202314978,31262705676958,38431148381142,
   46849676186200,56637093594452,67900189008898,80727405633478,95182068687240,111295445908064,
   129059977188214,148423058795676,169281802439190,191479200251240,214802105610192,238981384218450,
   263694503105880,288570712282050,313198838979824,337137562495508,359927876520902,381107288168832,
   400225163580712,416858522448594,430627517162136,441209811755794,448353104097810,451885112746692,
   451720475537386,447864173425816,440411288403368,429543112885068,415519833700338,398670202112650,
   379378760090278,358071312624982,335199408860532,311224616781060,286603346977922,261772905038780,
   237139338067050,213067500116950,189873606173218,167820386463374,147114802903332,127908156386266,
   110298304722862,94333631430564,80018357680772,67318773074544,56169972425794,46482720360272,
   38150117261490,31053802722016,25069500393798,20071775874386,15937942743478,12551107722570,
   9802391839104,7592399198846,5832028355636,4442734101008,3356351247876,2514588498934,
   1868291710858,1376563612626,1005812898070,728790895662,523659745830,373122941566,263637715946,
   184719363504,128340230206,88420705644,60405886422,40919368090,27484559796,18303705000,
   12085174666,7910361922,5132479750,3300623878,2103519382,1328364472,831081210,515061646,316154770,
   192178000,115668496,68926368,40660664,23743876,13724474,7852270,4446798,2492636,1383064,759644,
   413020,222298,118434,62454,32588,16810,8564,4304,2124,1020,472,210,84,28,6,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0]
end

public section

private abbrev fN {α : Type} (x : ℕ) (k : ℕ → α) : α := HighDForce.withForcedNat x k
private abbrev fL {α β : Type} (xs : List α) (k : List α → β) : β := HighDForce.withForcedList xs k
private theorem n1a (x : ℕ) : Nat.add 1 x = x + 1 := by rw [Nat.add_eq]; exact Nat.add_comm 1 x
private theorem ndiv (x y : ℕ) : Nat.div x y = x / y := rfl
private def uConsNat (x : ℕ) (xs : List ℕ) : List ℕ := match Nat.add 1 x with
  | 0 => xs
  | v + 1 => match xs with | [] => [v] | h :: t => v :: h :: t
private theorem uConsNat_eq (x : ℕ) (xs : List ℕ) : uConsNat x xs = x :: xs := by
  unfold uConsNat; rw [n1a]; cases xs <;> rfl
private def uToNatHb : List ℤ → Option (List ℕ)
  | [] => some []
  | x :: xs => match x with
    | Int.ofNat n => match uToNatHb xs with | some ns => some (uConsNat n ns) | none => none
    | Int.negSucc _ => none
private def uOfNatHb : List ℕ → List ℤ
  | [] => []
  | n :: ns => Int.ofNat n :: uOfNatHb ns
private theorem uToNatHb_sound :
    ∀ (hb : List ℤ) (ns : List ℕ), uToNatHb hb = some ns → hb = uOfNatHb ns
  | [], ns, h => by injection h with h'; subst h'; rfl
  | Int.negSucc _ :: _, _, h => by dsimp only [uToNatHb] at h; cases h
  | Int.ofNat n :: xs, ns, h => by
    dsimp only [uToNatHb] at h; revert h; cases hxs : uToNatHb xs with
    | none => intro h; dsimp only at h; cases h
    | some ms =>
      intro h; dsimp only at h; injection h with h'; subst h'
      rw [uConsNat_eq, uOfNatHb, uToNatHb_sound xs ms hxs]
private def bConsZ (x : ℤ) (xs : List ℤ) : List ℤ := match x with
  | Int.ofNat v => match xs with | [] => [Int.ofNat v] | h :: t => Int.ofNat v :: h :: t
  | Int.negSucc v => match xs with | [] => [Int.negSucc v] | h :: t => Int.negSucc v :: h :: t
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
    match Nat.sub z (Nat.add k 1) with | 0 => none | w + 1 => some (Nat.add w 1)
private def bEnc (z : ℕ) : List ℤ → Option (List ℕ)
  | [] => some []
  | x :: xs => match bEnc1 z x with
    | none => none
    | some u => match bEnc z xs with | none => none | some us => some (uConsNat u us)
private theorem bEnc1_sound (z : ℕ) (x : ℤ) (u : ℕ) (h : bEnc1 z x = some u) :
    ((u : ℤ) - (z : ℤ)) = x := by
  cases x with
  | ofNat n =>
    unfold bEnc1 at h; injection h with h'; subst h'; rw [Nat.add_eq, Int.ofNat_eq_natCast]; omega
  | negSucc k =>
    unfold bEnc1 at h; simp only [Nat.sub_eq, Nat.add_eq] at h
    revert h; cases hz : z - (k + 1) with
    | zero => intro h; dsimp only at h; cases h
    | succ w =>
      intro h; dsimp only at h; injection h with h'; subst h'; rw [Int.negSucc_eq]; omega
private theorem bEnc_sound (z : ℕ) :
    ∀ (xs : List ℤ) (us : List ℕ), bEnc z xs = some us → bDec z us = xs
  | [], us, h => by injection h with h'; subst h'; rfl
  | x :: xs, us, h => by
    dsimp only [bEnc] at h; revert h; cases hx : bEnc1 z x with
    | none => intro h; dsimp only at h; cases h
    | some u =>
      dsimp only; cases hxs : bEnc z xs with
      | none => intro h; dsimp only at h; cases h
      | some ws =>
        intro h; dsimp only at h; injection h with h'; subst h'
        rw [uConsNat_eq, bDec_cons, bEnc1_sound z x u hx, bEnc_sound z xs ws hxs]
private def zTdiv (x : ℤ) (d : ℕ) : ℤ :=
  match x with | Int.ofNat m => Int.ofNat (m / d) | Int.negSucc k => -(((k + 1) / d : ℕ) : ℤ)
private theorem bNeg_eq : ∀ (n : ℕ), muxRawNegOfNat n = -(n : ℤ)
  | 0 => by dsimp only [muxRawNegOfNat]; rw [Int.ofNat_eq_natCast]; omega
  | k + 1 => by dsimp only [muxRawNegOfNat]; rw [Int.negSucc_eq]; omega
private theorem bTdivNat_eq : ∀ (x : ℤ) (d : ℕ), muxRawIntTdivNat x d = zTdiv x d
  | Int.ofNat _, _ => rfl
  | Int.negSucc k, d => by dsimp only [muxRawIntTdivNat, zTdiv]; rw [bNeg_eq, ndiv, Nat.add_eq]
private theorem bSubNatTdiv_eq (m n d : ℕ) :
    rkmUltraSubNatTdiv m n d = zTdiv ((m : ℤ) - (n : ℤ)) d := by
  unfold rkmUltraSubNatTdiv; simp only [Nat.sub_eq, ndiv, Nat.add_eq]; cases h : n - m with
  | zero =>
    have hm : (m : ℤ) - (n : ℤ) = Int.ofNat (m - n) := by rw [Int.ofNat_eq_natCast]; omega
    rw [hm]; rfl
  | succ k =>
    dsimp only
    have hm : (m : ℤ) - (n : ℤ) = Int.negSucc k := by rw [Int.negSucc_eq]; omega
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
      dsimp only [rkmUltraSubTdiv]; rw [hm]; dsimp only [zTdiv]
      rw [bNeg_eq, ndiv, Nat.add_eq, Nat.add_eq]
      exact congrArg (fun t : ℕ => -(((t / d : ℕ) : ℤ))) (by omega)
    | negSucc n =>
      dsimp only [rkmUltraSubTdiv]; rw [bSubNatTdiv_eq, Nat.add_eq, Nat.add_eq]
      exact congrArg (fun t => zTdiv t d) (by simp only [Int.negSucc_eq]; omega)
private theorem bMul_eq : ∀ (a b : ℤ), muxRawIntMul a b = a * b
  | Int.ofNat m, Int.ofNat n => by
    dsimp only [muxRawIntMul]; rw [Nat.mul_eq]; simp only [Int.ofNat_eq_natCast]; push_cast; ring
  | Int.ofNat m, Int.negSucc n => by
    dsimp only [muxRawIntMul]
    rw [bNeg_eq, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]; push_cast; ring
  | Int.negSucc m, Int.ofNat n => by
    dsimp only [muxRawIntMul]
    rw [bNeg_eq, Nat.mul_eq, Nat.add_eq, Int.negSucc_eq, Int.ofNat_eq_natCast]; push_cast; ring
  | Int.negSucc m, Int.negSucc n => by
    dsimp only [muxRawIntMul]; rw [Nat.mul_eq, Nat.add_eq, Nat.add_eq, Int.ofNat_eq_natCast]
    simp only [Int.negSucc_eq]; push_cast; ring
private theorem bForcedAdd_eq : ∀ (a b : ℤ), rkmForcedIntAdd a b = a + b
  | Int.ofNat m, Int.ofNat n => by
    dsimp only [rkmForcedIntAdd]; rw [bOfNatF_eq, Nat.add_eq]
    simp only [Int.ofNat_eq_natCast]; omega
  | Int.ofNat m, Int.negSucc n => by
    dsimp only [rkmForcedIntAdd]; rw [bSub_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
    omega
  | Int.negSucc m, Int.ofNat n => by
    dsimp only [rkmForcedIntAdd]; rw [bSub_eq, Nat.add_eq, Int.negSucc_eq, Int.ofNat_eq_natCast]
    omega
  | Int.negSucc m, Int.negSucc n => by
    dsimp only [rkmForcedIntAdd]; rw [bNegSuccF_eq, Nat.add_eq, Nat.add_eq]
    simp only [Int.negSucc_eq]; omega
private theorem bAddCons_eq (a b : ℤ) (xs : List ℤ) : rkmUltraAddCons a b xs = (a + b) :: xs := by
  unfold rkmUltraAddCons; rw [bForcedAdd_eq]; cases a + b <;> cases xs <;> rfl
private def bStepVal (v P Q d : ℕ) : ℕ := match Nat.sub Q P with
  | 0 => Nat.add v (Nat.div (Nat.sub P Q) d)
  | k + 1 => Nat.sub v (Nat.div (Nat.add k 1) d)
private theorem bStepVal_eq (z v P Q d : ℕ) (hv : 0 < bStepVal v P Q d) :
    ((bStepVal v P Q d : ℤ) - (z : ℤ)) = ((v : ℤ) - (z : ℤ)) + zTdiv ((P : ℤ) - (Q : ℤ)) d := by
  rw [← bSubNatTdiv_eq]; unfold bStepVal at hv ⊢; unfold rkmUltraSubNatTdiv
  simp only [Nat.sub_eq, Nat.add_eq, ndiv] at hv ⊢; revert hv; cases h : Q - P with
  | zero => intro _; dsimp only; rw [Int.ofNat_eq_natCast]; push_cast; ring
  | succ k => intro hv; dsimp only at hv ⊢; rw [bNeg_eq]; omega
private abbrev bCellVal (z d b0 c0 b v c1 : ℕ) : ℕ :=
  bStepVal v (Nat.add (Nat.mul b0 c0) (Nat.mul b z)) (Nat.add (Nat.mul b c1) (Nat.mul b0 z)) d
private theorem bCell_hb (z d b0 c0 b v c1 : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hv : 0 < bCellVal z d b0 c0 b v c1) (ht : bDec z rest = tailZ) :
    bDec z (uConsNat (bCellVal z d b0 c0 b v c1) rest) = rkmUltraAddCons ((v : ℤ) - (z : ℤ))
      (rkmUltraSubTdiv (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
        (muxRawIntMul (Int.ofNat b) ((c1 : ℤ) - (z : ℤ))) d) tailZ := by
  rw [uConsNat_eq, bDec_cons, ht, bAddCons_eq, bSubTdiv_eq, bMul_eq, bMul_eq]
  refine congrArg (· :: tailZ) ?_
  have hpq : ((Nat.add (Nat.mul b0 c0) (Nat.mul b z) : ℕ) : ℤ) -
      ((Nat.add (Nat.mul b c1) (Nat.mul b0 z) : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) - (Int.ofNat b) * ((c1 : ℤ) - (z : ℤ)) := by
    simp only [Nat.add_eq, Nat.mul_eq, Int.ofNat_eq_natCast]; push_cast; ring
  unfold bCellVal at hv ⊢; rw [bStepVal_eq z v _ _ d hv, hpq]
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
private theorem bAllPos_cons {x : ℕ} {xs : List ℕ} (h : bAllPos (x :: xs) = true) :
    0 < x ∧ bAllPos xs = true := by
  cases x with | zero => exact Bool.noConfusion h | succ k => exact ⟨Nat.succ_pos k, h⟩
private theorem bAllPos_uCons {x : ℕ} {xs : List ℕ} (h : bAllPos (uConsNat x xs) = true) :
    0 < x ∧ bAllPos xs = true := by rw [uConsNat_eq] at h; exact bAllPos_cons h
private def bHeadOr (z : ℕ) : List ℕ → ℕ
  | [] => z
  | x :: _ => x
private def bTailN : List ℕ → List ℕ
  | [] => []
  | _ :: xs => xs
private theorem bHeadOr_eq (z : ℕ) : ∀ (cs : List ℕ),
    ((bHeadOr z cs : ℤ) - (z : ℤ)) = (match bDec z cs with | cn :: _ => cn | [] => Int.ofNat 0)
  | [] => by unfold bHeadOr; rw [bDec_nil, bZero_eq]
  | c :: cs => by unfold bHeadOr; rw [bDec_cons]
private theorem bTailN_eq (z : ℕ) : ∀ (xs : List ℕ),
    bDec z (bTailN xs) = (match bDec z xs with | _ :: t => t | [] => [])
  | [] => rfl
  | x :: xs => by unfold bTailN; rw [bDec_cons]
private def bSlide (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, b0, c0, bns, vs, cs => match bns with
    | [] => uConsNat (bStepVal (bHeadOr z vs) (Nat.mul b0 c0) (Nat.mul b0 z) d)
        (bSlide z d rem 0 z [] (bTailN vs) (bTailN cs))
    | b :: bR => match vs, cs with
      | v :: vT, c :: cT =>
        uConsNat (bCellVal z d b0 c0 b v (bHeadOr z cT)) (bSlide z d rem b c bR vT cT)
      | v :: vT, [] => uConsNat (bCellVal z d b0 c0 b v z) (bSlide z d rem b z bR vT [])
      | [], c :: cT =>
        uConsNat (bCellVal z d b0 c0 b z (bHeadOr z cT)) (bSlide z d rem b c bR [] cT)
      | [], [] => uConsNat (bCellVal z d b0 c0 b z z) (bSlide z d rem b z bR [] [])
private theorem bSlide_sound (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bAllPos (bSlide z d rem b0 c0 bns vs cs) = true → bDec z (bSlide z d rem b0 c0 bns vs cs) =
      rkmUltraSlideLoopAux d rem (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
        (uOfNatHb bns) (bDec z vs) (bDec z cs)
  | 0, _, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, bns, vs, cs, h => by
    cases bns with
    | nil =>
      dsimp only [bSlide, uOfNatHb, rkmUltraSlideLoopAux] at h ⊢; have hp := bAllPos_uCons h
      have hi := bSlide_sound z d rem 0 z [] (bTailN vs) (bTailN cs) hp.2
      rw [bMul0, uOfNatHb, bTailN_eq z vs, bTailN_eq z cs] at hi
      have hc := bCell_nil z d b0 c0 (bHeadOr z vs) hp.1 hi; rw [bHeadOr_eq z vs] at hc; exact hc
    | cons b bR =>
      cases vs with
      | nil => cases cs with
        | nil =>
          dsimp only [bSlide, uOfNatHb] at h ⊢; rw [bDec_nil]
          dsimp only [rkmUltraSlideLoopAux]; have hp := bAllPos_uCons h
          have hi := bSlide_sound z d rem b z bR [] [] hp.2
          rw [bZero_eq z, bDec_nil] at hi; have hc := bCell_hb z d b0 c0 b z z hp.1 hi
          rw [bZero_eq z] at hc; exact hc
        | cons c cT =>
          dsimp only [bSlide, uOfNatHb] at h ⊢; rw [bDec_nil, bDec_cons z c cT]
          dsimp only [rkmUltraSlideLoopAux]; have hp := bAllPos_uCons h
          have hi := bSlide_sound z d rem b c bR [] cT hp.2; rw [bDec_nil] at hi
          have hc := bCell_hb z d b0 c0 b z (bHeadOr z cT) hp.1 hi
          rw [bHeadOr_eq z cT, bZero_eq z] at hc; exact hc
      | cons v vT => cases cs with
        | nil =>
          dsimp only [bSlide, uOfNatHb] at h ⊢; rw [bDec_cons z v vT, bDec_nil]
          dsimp only [rkmUltraSlideLoopAux]; have hp := bAllPos_uCons h
          have hi := bSlide_sound z d rem b z bR vT [] hp.2; rw [bZero_eq z, bDec_nil] at hi
          have hc := bCell_hb z d b0 c0 b v z hp.1 hi; rw [bZero_eq z] at hc; exact hc
        | cons c cT =>
          dsimp only [bSlide, uOfNatHb] at h ⊢; rw [bDec_cons z v vT, bDec_cons z c cT]
          dsimp only [rkmUltraSlideLoopAux]; have hp := bAllPos_uCons h
          have hi := bSlide_sound z d rem b c bR vT cT hp.2
          have hc := bCell_hb z d b0 c0 b v (bHeadOr z cT) hp.1 hi
          rw [bHeadOr_eq z cT] at hc; exact hc
private def bStg (z dg mL cL : ℕ) (bns vns cns : List ℕ) : Option (List ℕ) :=
  fN (rkmNextLen mL cL) fun nL => fN (Nat.mul dg wdScale) fun d =>
    fL (bSlide z d nL 0 z bns vns cns) fun out => cond (bAllPos out) (some out) none
private theorem bStg_sound (z dg mL cL : ℕ) (bns vns cns out : List ℕ)
    (h : bStg z dg mL cL bns vns cns = some out) :
    bDec z out = rkmUltraHornerStage dg mL cL (uOfNatHb bns) (bDec z vns) (bDec z cns) := by
  unfold bStg at h; dsimp only [fN, fL] at h
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceList_eq] at h
  revert h
  cases hp : bAllPos (bSlide z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z bns vns cns) with
  | false => intro h; dsimp only [cond] at h; cases h
  | true =>
    intro h; injection h with h'; subst h'; unfold rkmUltraHornerStage
    rw [rkmb_forceNat_eq, rkmb_forceNat_eq, ← bMul0 z]
    exact bSlide_sound z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z bns vns cns hp
private def bBind (z dg mL cL : ℕ) (bns vns cns : List ℕ)
    (k : ℕ → List ℕ → Option (List ℕ)) : Option (List ℕ) :=
  fN (rkmNextLen mL cL) fun nL =>
    match bStg z dg mL cL bns vns cns with | none => none | some out => k nL out
private theorem bBind_sound {z dg mL cL : ℕ} {bns vns cns out : List ℕ}
    {kB : ℕ → List ℕ → Option (List ℕ)} {kU : ℕ → List ℤ → List ℤ}
    (h : bBind z dg mL cL bns vns cns kB = some out)
    (hk : ∀ (mid : List ℕ), kB (rkmNextLen mL cL) mid = some out →
      bDec z out = kU (rkmNextLen mL cL) (bDec z mid)) :
    bDec z out = (HighDForce.withForcedNat (rkmNextLen mL cL) fun nL =>
      HighDForce.withForcedList
        (rkmUltraHornerStage dg mL cL (uOfNatHb bns) (bDec z vns) (bDec z cns)) (kU nL)) := by
  unfold bBind at h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h
  revert h; cases hs : bStg z dg mL cL bns vns cns with
  | none => intro h; dsimp only at h; cases h
  | some mid =>
    intro h; rw [rkmb_forceNat_eq, rkmb_forceList_eq, ← bStg_sound z dg mL cL bns vns cns mid hs]
    exact hk mid h
private def bStep (z mL c : ℕ) (bns vns : List ℕ) : Option (List ℕ) :=
  bBind z 16 mL c bns vns vns fun l1 c1 => bBind z 15 mL l1 bns vns c1 fun l2 c2 =>
  bBind z 14 mL l2 bns vns c2 fun l3 c3 => bBind z 13 mL l3 bns vns c3 fun l4 c4 =>
  bBind z 12 mL l4 bns vns c4 fun l5 c5 => bBind z 11 mL l5 bns vns c5 fun l6 c6 =>
  bBind z 10 mL l6 bns vns c6 fun l7 c7 => bBind z 9 mL l7 bns vns c7 fun l8 c8 =>
  bBind z 8 mL l8 bns vns c8 fun l9 c9 => bBind z 7 mL l9 bns vns c9 fun la ca =>
  bBind z 6 mL la bns vns ca fun lb cb => bBind z 5 mL lb bns vns cb fun lc cc =>
  bBind z 4 mL lc bns vns cc fun ld cd => bBind z 3 mL ld bns vns cd fun le ce =>
  bBind z 2 mL le bns vns ce fun lf cf => bStg z 1 mL lf bns vns cf
private theorem bStep_sound (z mL cL : ℕ) (bns vns out : List ℕ)
    (h : bStep z mL cL bns vns = some out) :
    bDec z out = rkmUltraHornerT16Step mL cL (uOfNatHb bns) (bDec z vns) := by
  unfold bStep at h; unfold rkmUltraHornerT16Step
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  exact bStg_sound _ _ _ _ _ _ _ _ h
private def bIter (z : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → Option (List ℕ)
  | 0, _, _, _, vns => some vns
  | k + 1, mL, cL, bns, vns => match bStep z mL cL bns vns with
    | none => none
    | some vNext => fN (rkmNextLen16 mL cL) fun nL => bIter z k mL nL bns vNext
private theorem bIter_sound (z : ℕ) : ∀ (k mL cL : ℕ) (bns vns out : List ℕ),
    bIter z k mL cL bns vns = some out →
    bDec z out = muxUltraIterFullT16Rkm k mL cL (uOfNatHb bns) (bDec z vns)
  | 0, _, _, _, vns, out, h => by injection h with h'; subst h'; rfl
  | k + 1, mL, cL, bns, vns, out, h => by
    unfold bIter at h; revert h; cases hs : bStep z mL cL bns vns with
    | none => intro h; dsimp only at h; cases h
    | some vNext =>
      intro h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h; unfold muxUltraIterFullT16Rkm
      rw [rkmb_forceList_eq, rkmb_forceNat_eq, ← bStep_sound z mL cL bns vns vNext hs]
      exact bIter_sound z k mL (rkmNextLen16 mL cL) bns vNext out h
private def fIter (k mL cL : ℕ) (hb v : List ℤ) : List ℤ :=
  let z := 100000000000000000
  match uToNatHb hb with
  | none => muxUltraIterFullT16Rkm k mL cL hb v
  | some bns => match bEnc z v with
    | none => muxUltraIterFullT16Rkm k mL cL hb v
    | some vns => match bIter z k mL cL bns vns with
      | none => muxUltraIterFullT16Rkm k mL cL hb v
      | some out => bDec z out
private theorem fIter_eq (k mL cL : ℕ) (hb v : List ℤ) :
    fIter k mL cL hb v = muxUltraIterFullT16Rkm k mL cL hb v := by
  unfold fIter; dsimp only; cases hh : uToNatHb hb with
  | none => rfl
  | some bns => dsimp only; cases hv : bEnc 100000000000000000 v with
    | none => rfl
    | some vns => dsimp only; cases hi : bIter 100000000000000000 k mL cL bns vns with
      | none => rfl
      | some out =>
        dsimp only; rw [bIter_sound 100000000000000000 k mL cL bns vns out hi,
          ← uToNatHb_sound hb bns hh, bEnc_sound 100000000000000000 v vns hv]
private def muxFastIterBSlideChk (steps maxLen : ℕ) (hb vecIn vecOut : List ℤ) : Bool :=
  fL hb fun hbF => fL vecIn fun inF => fL vecOut fun outF =>
    fN (altIntLen inF) fun len0 => muxIntListEq (fIter steps maxLen len0 hbF inF) outF
private theorem muxFastIterBSlideChk_sound {steps maxLen : ℕ} {hb vecIn vecOut : List ℤ}
    (h : muxFastIterBSlideChk steps maxLen hb vecIn vecOut = true) :
    muxFastIterFullT16 steps maxLen hb vecIn = vecOut := by
  unfold muxFastIterBSlideChk at h; dsimp only [fL, fN] at h
  rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq] at h
  rw [rkmb_forceNat_eq, fIter_eq] at h
  have h2 : muxUltraIterFullT16HiChk steps 0 maxLen hb vecIn vecOut = true := by
    unfold muxUltraIterFullT16HiChk; dsimp only
    rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceNat_eq]
    exact h
  exact muxUltraIterFullT16HiChk_sound h2
private theorem rkmHd {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : b = true := (rkmAllTrueF_cons h).1
private theorem rkmTl {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : rkmAllTrueF bs = true :=
  (rkmAllTrueF_cons h).2
private def pzig : List ℕ → List ℤ
  | [] => []
  | w :: ws =>
    (match Nat.mod w 2 with
     | 0 => primOfNatForced (Nat.div w 2)
     | _ => primNegSuccForced (Nat.div w 2)) :: pzig ws
private def phbv_w0_p0 : List ℤ := pzig
  [171077973331968,241468249503688,295158258500214,340151126663952,379553368621432,
   414961419204382,447325517093920,477266011739190,505214639995968,531486356966650,
   556319387916318,579899166700420,602373442334834,623862238580672,644464661182770,
   664263693328032,683329661943544,701722799438314,719495173880036,736692168229788,
   753353631184418,769514784642544,785206947950104,800458122252242,815293466660160,
   829735689777446,843805374300612,857521248183998,870900412756626,883958535871638,
   896710016433916,909168125332872,921345126795236,933252383388814,944900447295842,
   956299139992368,967457622087682,978384454772244,989087654076882,999574738947222,
   1009852773975562,1019928407499950,1029807905671252,1039497182999018,1049001829811992,
   1058327137006756,1067478118405618,1076459531000782,1085275893324672,1093931502154678,
   1102430447733770,1110776627665436,1118973759621834,1127025392987052,1134934919542908,
   1142705583292054,1150340489502300,1157842613046530,1165214806104340,1172459805284318,
   1179580238219508,1186578629683086,1193457407266390,1200218906657088,1206865376551512,
   1213398983231794,1219821814835426,1226135885342248,1232343138301464,1238445450319196,
   1244444634325178,1250342442635542,1256140569827056,1261840655436926,1267444286500920,
   1272952999941602,1278368284817350,1283691584442030,1288924298384316,1294067784354964,
   1299123359989632,1304092304534278,1308975860439590,1313775234870390,1318491601135532,
   1323126100043382,1327679841187562,1332153904167338,1336549339746660,1340867170955628,
   1345108394137852,1349273979946912,1353364874294970,1357381999256274,1361326253928208,
   1365198515252290,1368999638797390,1372730459507274,1376391792414480,1379984433322320,
   1383509159456800,1386966730090034,1390357887136662,1393683355724744,1396943844742406,
   1400140047361524,1403272641539612,1406342290501022,1409349643198484,1412295334755992,
   1415179986893918,1418004208337252,1420768595207772,1423473731400926,1426120188948134,
   1428708528365210,1431239298987568,1433713039292784,1436130277211138,1438491530424654,
   1440797306655168,1443048103941924,1445244410909148,1447386707024040,1449475462845630,
   1451511140264852,1453494192736260,1455425065501688]
private def phbv_w0_p1 : List ℤ := pzig
  [1457304195806264,1459132013107018,1460908939274470,1462635388787438,1464311768921346,
   1465938479930344,1467515915223418,1469044461534794,1470524499088822,1471956401759590,
   1473340537225440,1474677267118616,1475966947170212,1477209927350612,1478406552005580,
   1479557159988192,1480662084786716,1481721654648664,1482736192701076,1483706017067242,
   1484631440979956,1485512772891432,1486350316580020,1487144371253812,1487895231651268,
   1488603188138950,1489268526806486,1489891529558848,1490472474206030,1491011634550232,
   1491509280470628,1491965678005790,1492381089433870,1492755773350596,1493089984745150,
   1493383975074032,1493637992332926,1493852281126682,1494027082737450,1494162635191010,
   1494259173321408,1494316928833888,1494336130366228,1494317003548500,1494259771061300,
   1494164652692530,1494031865392740,1493861623329080,1493654137937936,1493409617976246,
   1493128269571564,1492810296270910,1492455899088426,1492065276551882,1491638624748070,
   1491176137367120,1490678005745760,1490144418909546,1489575563614126,1488971624385518,
   1488332783559462,1487659221319870,1486951115736382,1486208642801080,1485431976464344,
   1484621288669934,1483776749389246,1482898526654832,1481986786593152,1481041693456630,
   1480063409654966,1479052095785808,1478007910664710,1476931011354480,1475821553193878,
   1474679689825692,1473505573224228,1472299353722214,1471061180037134,1469791199296998,
   1468489557065598,1467156397367214,1465791862710820,1464396094113792,1462969231125124,
   1461511411848176,1460022772962954,1458503449747950,1456953576101528,1455373284562892,
   1453762706332640,1452121971292892,1450451208027046,1448750543839124,1447020104772756,
   1445260015629776,1443470399988480,1441651380221512,1439803077513422,1437925611877876,
   1436019102174548,1434083666125684,1432119420332362,1430126480290440,1428104960406206,
   1426054974011750,1423976633380024,1421870049739658,1419735333289470,1417572593212746,
   1415381937691222,1413163473918848,1410917308115278,1408643545539134,1406342290501022,
   1404013646376316,1401657715617732,1399274599767654,1396864399470264,1394427214483448,
   1391963143690502,1389472285111624,1386954735915222,1384410592429012,1381839950150940,
   1379242903759900,1376619547126288,1373969973322368]
private def phbv_w0_p2 : List ℤ := pzig
  [1371294274632454,1368592542562944,1365864867852164,1363111340480056,1360332049677706,
   1357527083936718,1354696531018420,1351840477962938,1348959011098102,1346052216048218,
   1343120177742706,1340162980424572,1337180707658772,1334173442340422,1331141266702894,
   1328084262325762,1325002510142640,1321896090448888,1318765082909202,1315609566565078,
   1312429619842156,1309225320557474,1305996745926576,1302743972570530,1299467076522842,
   1296166133236246,1292841217589406,1289492403893510,1286119765898764,1282723376800786,
   1279303309246910,1275859635342390,1272392426656512,1268901754228614,1265387688574028,
   1261850299689908,1258289657061002,1254705829665324,1251098885979740,1247468893985480,
   1243815921173568,1240140034550174,1236441300641882,1232719785500894,1228975554710154,
   1225208673388388,1221419206195094,1217607217335446,1213772770565124,1209915929195102,
   1206036756096330,1202135313704390,1198211664024054,1194265868633804,1190297988690274,
   1186308084932634,1182296217686920,1178262446870292,1174206831995252,1170129432173780,
   1166030306121444,1161909512161426,1157767108228512,1153603151873016,1149417700264668,
   1145210810196432,1140982538088282,1136732939990928,1132462071589490,1128169988207130,
   1123856744808626,1119522396003904,1115166996051532,1110790598862152,1106393258001878,
   1101975026695656,1097535957830562,1093076103959080,1088595517302316,1084094249753188,
   1079572352879568,1075029877927384,1070466875823682,1065883397179658,1061279492293636,
   1056655211154024,1052010603442224,1047345718535510,1042660605509864,1037955313142790,
   1033229889916076,1028484384018534,1023718843348708,1018933315517532,1014127847850980,
   1009302487392666,1004457280906412,999592274878800,994707515521680,989803048774648,
   984878920307502,979935175522666,974971859557574,969989017287050,964986693325632,
   959964932029886,954923777500694,949863273585496,944783463880536,939684391733048,
   934566100243446,929428632267470,924272030418312,919096337068722,913901594353088,
   908687844169480,903455128181694,898203487821250,892932964289382,887643598558996,
   882335431376612,877008503264288,871662854521502,866298525227042,860915555240848,
   855513984205856,850093851549806,844655196487028]
private def phbv_w0_p3 : List ℤ := pzig
  [839198058020230,833722474942236,828228485837730,822716129084970,817185442857474,
   811636465125712,806069233658758,800483786025928,794880159598410,789258391550864,
   783618518863016,777960578321226,772284606520044,766590639863742,760878714567848,
   755148866660640,749401131984636,743635546198076,737852144776370,732050963013550,
   726232036023686,720395398742310,714541085927804,708669132162790,702779571855498,
   696872439241112,690947768383124,685005593174648,679045947339742,673068864434702,
   667074377849352,661062520808314,655033326372266,648986827439196,642923056745630,
   636842046867862,630743830223150,624628439070928,618495905513984,612346261499634,
   606179538820886,599995769117590,593794983877572,587577214437768,581342491985340,
   575090847558778,568822312048994,562536916200408,556234690612022,549915665738480,
   543579871891122,537227339239026,530858097810036,524472177491794,518069608032736,
   511650419043114,505214639995968,498762300228124,492293428941164,485808055202390,
   479306207945772,472787915972908,466253207953948,459702112428534,453134657806710,
   446550872369836,439950784271492,433334421538370,426701812071162,420052983645434,
   413387963912496,406706780400264,400009460514114,393296031537726,386566520633918,
   379820954845482,373059361096000,366281766190666,359488196817082,352678679546072,
   345853240832458,339011907015860,332154704321468,325281658860810,318392796632522,
   311488143523098,304567725307654,297631567650654,290679696106660,283712136121058,
   276728913030782,269730052065036,262715578345994,255685516889522,248639892605860,
   241578730300322,234502054673988,227409890324376,220302261746118,213179193331632,
   206040709371782,198886834056538,191717591475626,184533005619170,177333100378342,
   170117899545984,162887426817250,155641705790214,148380759966512,141104612751928,
   133813287457024,126506807297730,119185195395950,111848474780146,104496668385936,
   97129799056664,89747889543994,82350962508464,74939040520072,67512146058830,60070301515320,
   52613529191256,45141851300032,37655289967260,30153867231318,22637605043882,15106525270460,
   7560649690916]
private def phbv_w0 : List ℤ := phbv_w0_p0 ++ (phbv_w0_p1 ++ (phbv_w0_p2 ++ phbv_w0_p3))
private def pvm_w0_1_p0 : List ℤ := pzig
  [14,12,8,11,12,12,10,2,16,20,8,18,22,25,326,1173,3996,9587,13542,12240,138297,454714,944599,
   1383560,1355235,331339,9716610,48169611,165133310,409036153,739444298,994392397,1045117780,
   1262415111,2767170298,7221608293,16390367654,27973476265,33548211512,24099507363,829196249,
   21667231978,10324824047,14990481459,5921448434,6012446232,13251816585,24770980193,17160146945,
   4090811648,31726593718,64248171588,105311809432,161379591998,240663609474,353353065688,
   512418435768,734578641530,1041315941238,1459935403918,2024671587204,2777819977592,
   3770843912628,5065384470154,6734080797798,8861091541506,11542195564474,14884343914340,
   19004537126996,24027914443404,30084965901192,37307815338018,45825571888654,55758808145442,
   67213292032842,80273172570800,94993891872514,111395160911298,129454388389068,149100984221382,
   170211966303640,192609277369896,216059165923408,240273901864096,264915986657958,
   289604885411874,313926162092412,337442749205712,359707940417524,380279569830922,
   398734745090730,414684441486252,427787246509624,437761571443428,444395717559568,
   447555295014838,447187635025196,443323000410820,436072574540590,425623381862568,
   412230452797168,396206681378106,377910927425734,357734980760460,336090030606786,
   313393269581244,290055212009108,266468226634044,242996681631234,219968983735378,
   197671671985122,176345608311144,156184199130020,137333489910534,119893902254372,
   103923332430042,89441301807294,76433841999282,64858808234894,54651340183892,45729226284652,
   37997971586170,31355416407268,25695800352068,20913210620562,16904393019626,13570937230208,
   10820874008686]
private def pvm_w0_1_p1 : List ℤ := pzig
  [8569740976134,6741185841338,5267182027444,4087932679586,3151535984396,2413478712368,
   1836016920986,1387493731276,1041634768604,776852819120,575584958672,423677981800,309832127006,
   225106779334,162492145362,116535176704,83042297766,58786231260,41366056594,28894392086,
   20089606038,13846921984,9495418864,6488163976,4372006992,2942643376,1985401786,1311189922,
   852268590,564188820,379237870,248736546,154824506,91262654,50964572,26785538,13404008,6824606,
   3908862,2595318,1896990,1442144,1073286,729228,425818,203150,74104,17778,1672,850,2788,3630,
   3272,2414,1570,940,526,278,134,58,20,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_1_p2 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_1_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_1_p4 : List ℤ := pzig
  [0]
private def pvm_w0_1 : List ℤ :=
  pvm_w0_1_p0 ++ (pvm_w0_1_p1 ++ (pvm_w0_1_p2 ++ (pvm_w0_1_p3 ++ pvm_w0_1_p4)))
private def pvm_w0_2_p0 : List ℤ := pzig
  [14,12,20,5,5,2,16,6,20,101,404,1033,1766,580,17535,77290,218605,422340,371599,1163929,7734976,
   28053185,80307838,194783827,406777142,736516103,1185355870,1825608903,3031598392,5676602681,
   10819090278,18494319603,26083315784,27982674951,18749358652,373854974,17320417251,16793269814,
   1449673396,15993984213,7308097716,11853902768,9326001999,10240518787,7427041148,10556541418,
   2823616203,9838235371,2080141417,7706422090,6539949824,5194573327,18024525205,23498046869,
   18998222315,6283853239,12055926870,35023052160,63906210488,102040529710,154469132230,
   227900475710,331003038698,474945907072,674094916900,946811788940,1316330821758,1811695271310,
   2468729285374,3331008139110,4450773924296,5889728076920,7719617593396,10022519780968,
   12890722366720,16426093364290,20738839874804,25945568399420,32166582273612,39522384890864,
   48129400062100,58094971813456,69511762824240,82451730241544,96959915637324,113048337667140,
   130690316566680,149815584177256,170306537562028,191995975401782,214666612716762,
   238052601361988,261843193524532,285688577465566,309207795172940,331998528032360,
   353648417582272,373747482600352,391901109363260,407743035874616,420947728230000,
   431241560769146,438412261274350,442316165506958,442882936594774,440117536828740,
   434099383421066,424978766048888,412970742889184,398346854444844,381425093325240,
   362558637817814,342123894442104,320508399034004,298099098954806,275271484526628,
   252379961184470,229749761634040,207670596566662,186392140207144,166121349582320,
   147021529330048,129212981265164,112775022480626,97749118715880,84142860921196,71934511071114,
   61077856031616]
private def pvm_w0_2_p1 : List ℤ := pzig
  [51507132920366,43141822274942,35891144434252,29658133290246,24343206542962,19847176977954,
   16073710582578,12931202251278,10334192495706,8204207904294,6470384883004,5069456142008,
   3945885854078,3051269648884,2344136480902,1789204487196,1356775638570,1022243324648,
   765228175766,569135232722,420603573096,308843140288,225314995206,163348182352,117678441800,
   84223050548,59897741502,42344050424,29745022786,20751326702,14385622648,9919882520,6801609570,
   4628842630,3124305096,2095513316,1401281778,935710304,622412408,409740922,264575426,166068882,
   100659350,58788490,33209562,18362718,10169562,5836508,3582684,2358956,1609792,1084508,693528,
   411030,223128,110750,50910,22644,10734,6062,4086,2968,2132,1452,932,560,316,166,78,30,8,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0]
private def pvm_w0_2_p2 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_2_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_2_p4 : List ℤ := pzig
  [0]
private def pvm_w0_2 : List ℤ :=
  pvm_w0_2_p0 ++ (pvm_w0_2_p1 ++ (pvm_w0_2_p2 ++ (pvm_w0_2_p3 ++ pvm_w0_2_p4)))
private def pvm_w0_3_p0 : List ℤ := pzig
  [14,12,22,12,6,41,102,161,475,4578,18439,45964,41717,268975,1906204,7832487,25243888,69085391,
   165979036,356665387,696979184,1267560727,2217881370,3859166851,6728245200,11379654541,
   17638764264,23516909175,24928243860,17764960711,2295280558,13656409950,18203515573,6405060082,
   10914863138,14716005931,116375574,13496161678,6504430771,10055767023,8721279560,7902154652,
   8677447151,7758314107,7062400756,8993921188,3506436357,9750964065,1731786377,7771729882,
   6483076802,2510151397,7822241395,3914654293,4593863852,9301114884,5771425094,4116022803,
   14933459193,21676512459,21946797939,15844909401,4635046965,10630566920,29942226050,
   54617149042,87299819030,131935781144,193865251260,280080207734,399633364060,564171764496,
   788571054242,1091652945072,1496970696152,2033644095490,2737217569758,3650504325804,
   4824367299298,6318375370668,8201261934902,10551103654118,13455131355208,17009083884250,
   21316020582506,26484520011128,32626212395560,39852621272354,48271325656430,57981496634046,
   69068909771014,81600584492284,95619250352064,111137884103482,128134596691544,146548171816856,
   166274564082548,187164652283000,209023510612422,231611407367012,254646668578878,
   277810456066476,300753410242942,323104003576326,344478347600062,364491101944950,
   382767054931796,398952887970776,412728605190270,423818108432450,431998427004980,
   437107170165614,439047854887772,437792866753310,433383931084652,425930096927892,
   415603360165536,402632166000742,387293128541528,369901380195460,350800013439326,
   330349097395354,308914748923746,286858697764824,264528749063728,242250438134486,
   220320163799044,198999857509870]
private def pvm_w0_3_p1 : List ℤ := pzig
  [178513410378366,159044568184520,140736614824458,123693091655304,107980139589544,
   93629303504152,80641515869040,68991212358012,58630798056020,49495302956736,41506542550772,
   34577372154366,28615343908860,23525824807960,19214890582154,15591446462268,12568883914406,
   10066460632512,8010045412210,6332518778518,4974028415356,3881858615146,3010063428574,
   2319101224170,1775342895426,1350429950382,1020677105494,766539446162,572040530184,
   424203979720,312584908842,228877417862,166535372354,120422158290,86533730942,61787348216,
   43838217196,30911915842,21666883158,15094798036,10448554442,7183470166,4905895652,3330839152,
   2250781704,1514770246,1014564882,674527504,443266162,286487180,181258790,111895194,67331222,
   39591310,22916782,13229036,7745760,4667116,2903758,1844644,1172208,729740,438152,251550,
   137876,72588,37292,19216,10292,5888,3600,2298,1486,942,574,332,180,90,36,10,2,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_3_p2 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_3_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_3_p4 : List ℤ := pzig
  [0]
private def pvm_w0_3 : List ℤ :=
  pvm_w0_3_p0 ++ (pvm_w0_3_p1 ++ (pvm_w0_3_p2 ++ (pvm_w0_3_p3 ++ pvm_w0_3_p4)))
private def pvm_w0_4_p0 : List ℤ := pzig
  [14,12,22,28,167,880,591,18995,161908,856235,3520910,12114089,36139276,95525241,227318660,
   494088105,996042698,1892966955,3438580136,5995384233,9919541150,15150286209,20499221008,
   23162715879,19549608710,8116224345,7240773203,17201193138,13484227175,1799708887,14438626742,
   10830101493,5190153519,13670956930,3182945153,11213912595,7649065520,7963120226,9187421951,
   5878783351,9209576206,5342682038,8413069931,6133056193,6753422392,7694097170,3752955313,
   8899814647,798121531,7961197932,5668979592,3593898825,7866924157,2779487603,5003499794,
   6949247702,1637533712,5177880625,7059496383,2472470191,4832389372,9421093322,8021136968,
   1017315578,8529843377,16928084205,21501092027,21182778293,16195117113,7304823427,4895110482,
   20462020494,40331624512,66399107144,101569891858,149863392198,216610979964,308758895480,
   435271501816,607625570208,840386073182,1151853820802,1564773001856,2107081724922,
   2812681297728,3722190887248,4883644123386,6353073952414,8194922493922,10482204777038,
   13296350092974,16726643406940,20869192901438,25825359213516,31699597970076,38596690128280,
   46618364215242,55859350072442,66402943762400,78316205864250,91644957881950,106408780873606,
   122596253380768,140160688973128,159016644167886,179037462625890,200054099725244,
   221855432242848,244190201753398,266770669175356,289277975811520,311369115793110,
   332685335914490,352861687344884,371537387191336,388366567079224,403028985654078,
   415240191747304,424760769256836,431404101024402,435042526595894,435611266786124,
   433110438368846,427604425513028,419219457020258,408138650620298,394595614398254,
   378866283920704]
private def pvm_w0_4_p1 : List ℤ := pzig
  [361259675475394,342108115888634,321756865801716,300554251755032,278842134011040,
   256947225298042,235173809884138,213797529099978,193060782543946,173169744110310,
   154292622406854,136559487234272,120063377733570,104862276595184,90982080038902,78420242872676,
   67149668707388,57122889611780,48276349144842,40534415904198,33813131265292,28023701949474,
   23075507599360,18878573862598,15345644562974,12393826758940,9945731885216,7930212466564,
   6282819227320,4945975080448,3868865964186,3007149347394,2322572420800,1782507726084,
   1359405813428,1030217032288,775839409090,580602654346,431774295630,319092986468,234351742622,
   171042888650,124055944262,89414496254,64047266084,45596218280,32262831552,22687390822,
   15852768948,11005704576,7592223772,5206280550,3550854496,2409656090,1626726250,1091286960,
   725987298,477588894,309709348,197422914,123469884,75738732,45657654,27174394,16083764,9548150,
   5727380,3482008,2139144,1317194,804560,482874,282862,161274,89636,48860,26412,14378,8000,4598,
   2728,1648,1002,598,348,190,92,38,12,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_4_p2 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_4_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_4_p4 : List ℤ := pzig
  [0]
private def pvm_w0_4 : List ℤ :=
  pvm_w0_4_p0 ++ (pvm_w0_4_p1 ++ (pvm_w0_4_p2 ++ (pvm_w0_4_p3 ++ pvm_w0_4_p4)))
private def pvm_w0_5_p0 : List ℤ := pzig
  [18,143,1950,16671,108554,564313,2439308,9010511,29031486,82915363,212831376,497207039,
   1069544012,2139201799,4000339290,6982358251,11247660192,16352595149,20696019024,21427120043,
   15684285582,3354210483,10474097855,16897044160,10059456211,5253578965,14808632644,8302063875,
   7320768579,13187286616,1615147393,11544452077,7257178944,7834763568,9636612275,4660469359,
   10141934010,2855000240,9868879563,2431461489,9287936506,3169094370,8358490021,4764866597,
   6711243136,6718883788,3885075583,8129089315,245206189,7671570802,4810242620,4231673175,
   7549644543,1598534841,5898013634,6422568812,46396644,6005566169,5738045835,43864104,
   5553770052,5905571828,1088543558,4749674747,7042931021,4109480713,2142413824,7896391398,
   9848177228,6795691608,194195019,8686172231,16084157891,20518411665,21160478019,18047464611,
   11652828655,2430770863,9533704816,24738819564,44380234838,70425655814,105704769764,
   154051771738,220519830048,311674248474,435964280044,604170600026,829923983668,1130288941304,
   1526402925748,2044156884442,2714896457008,3576115333714,4672103657772,6054505451860,
   7782730572270,9924159407796,12554073406048,15755242282610,19617100827662,24234454395238,
   29705665426510,36130289055846,43606154730002,52225910270496,62073098100838,73217833727778,
   85712260896730,99585877945552,114841057451108,131448792016656,149345196487692,168428596801940,
   188557991914842,209552400137958,231192053174898,253220715259802,275349912300740,
   297264509027550,318629702881912,339099434935632,358325424034948,375967142525160,
   391701811393742,405234193031960,416305981320144,424703883988796]
private def pvm_w0_5_p1 : List ℤ := pzig
  [430266511721870,432889592147796,432529058473664,429202313338574,422987308717340,
   414019467814586,402486934652016,388624073083250,372703548624522,355027618638132,
   335918756289010,315710003019256,294735675095106,273322591303462,251782051739780,
   230403027188626,209446656954818,189142015186270,169683326031228,151228639816978,
   133899727819700,117783084866786,102931987083626,89369344307184,77091061428706,66069785193820,
   56258896757702,47596501550248,40009237469722,33415850126778,27730467494826,22865456200742,
   18733806796968,15251084424348,12336975377712,9916421312158,7920357233824,6286122676228,
   4957619886920,3885258473804,3025713324848,2341542241930,1800721983366,1376145486278,
   1045099575226,788735421258,591550636758,440904669528,326580775422,240395989628,175854791586,
   127843701520,92367283964,66326162246,47334606086,33572032946,23661773400,16571738662,
   11533637872,7978661800,5487698366,3753705976,2553559252,1726849418,1159678838,772142730,
   508699448,330913964,212164626,133922880,83224672,50986538,30881780,18568834,11136734,6690324,
   4035352,2442892,1479696,892392,533018,313908,181782,103478,58044,32244,17864,9950,5614,3218,
   1868,1094,634,356,188,90,38,12,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_5_p2 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_5_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_5_p4 : List ℤ := pzig
  [0]
private def pvm_w0_5 : List ℤ :=
  pvm_w0_5_p0 ++ (pvm_w0_5_p1 ++ (pvm_w0_5_p2 ++ (pvm_w0_5_p3 ++ pvm_w0_5_p4)))
private def pvm_w0_6_p0 : List ℤ := pzig
  [7558,75679,502224,2558791,10660226,37656743,115588474,313954071,765168940,1690519389,
   3405466086,6255597881,10403475440,15409151381,19732228118,20663739703,15459361098,3874369119,
   9479409431,16193956740,10306328557,4300386139,14269450518,8952957839,6225509643,13247767576,
   3030143845,10787135499,8670185192,6178768520,10756371615,2158438613,10844998996,416629377,
   10250927027,1586390854,9669655530,1604620599,9292759587,673676068,8972495702,1060990256,
   8332143475,3383359713,6870047924,5825612464,4152709857,7532604243,169929406,7355757374,
   4211911868,4416761901,7067843259,829489049,6186270560,5749081716,1129888911,6504183199,
   4835237847,1651551990,6221432600,4687397540,1075291803,5635897587,5161451293,370007441,
   4650890378,6006654552,2814008072,2562500753,6470992311,6403815405,2323641507,3623314956,
   8472318762,9926675898,7227088604,1182480534,6411329257,13550605529,18645019375,20809603749,
   19836076361,15957645407,9542212043,813571927,10354058210,24569061550,43010576724,67507288100,
   100638263404,145877912006,207798551604,292336374704,407124609264,561891047558,768923785202,
   1043590860206,1404926218390,1876236816596,2485772392210,3267338893862,4260975735250,
   5513429890766,7078709179608,9018211271088,11400949387172,14303113447612,17807680049790,
   22003236831060,26982639697808,32841022613638,39673266575204,47571158916424,56619770208964,
   66893740031778,78453054501520,91338663956330,105568277334402,121132070343692,137989020440226,
   156063821935272,175244499850816,195381321093198,216286772521604,237736885394574,
   259474194708526,281211972750244]
private def pvm_w0_6_p1 : List ℤ := pzig
  [302639916890190,323431253422576,343250741393100,361763542802776,378644691247358,
   393588524280740,406317883055732,416592767570212,424217836630216,429048539721934,
   430995734568078,430028392803352,426174301145076,419518899750952,410202207160580,
   398413909211600,384386993791062,368390222119340,350719647462238,331689608646248,
   311623662166816,290845725580578,269671707671972,248401998026934,227315063144862,
   206662225158478,186663712790196,167506086281428,149340997718666,132285136567360,
   116421237846092,101800044904552,88443038323330,76345692033408,65481066343510,55803597054562,
   47252923626770,39757584446874,33238453697530,27611857565902,22792327856080,18694945734304,
   15237246421062,12340697907956,9931795057396,7942809230490,6312225164156,4984902833500,
   3912016617628,3050828865868,2364345013070,1820883938082,1393591185174,1059923284994,
   801130905300,601762364678,449199658060,333231851058,245667950980,179991472904,131058784848,
   94841421268,68209666292,48752495454,34628383384,24442252098,17144994112,11952769822,
   8283454336,5707470530,3910173526,2663153508,1802273854,1210806802,806513286,531855048,
   346725618,223187196,141757864,88846424,54997442,33684336,20463316,12365424,7451594,4485904,
   2698904,1621072,969890,576394,339338,197520,113588,64582,36384,20394,11418,6412,3628,2066,
   1172,658,360,188,88,36,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_6_p2 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_6_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_6_p4 : List ℤ := pzig
  [0]
private def pvm_w0_6 : List ℤ :=
  pvm_w0_6_p0 ++ (pvm_w0_6_p1 ++ (pvm_w0_6_p2 ++ (pvm_w0_6_p3 ++ pvm_w0_6_p4)))
private def pvm_w0_7_p0 : List ℤ := pzig
  [607710,4494295,22409564,87143685,280718298,774122771,1863119368,3953351247,7410900912,
   12191448985,17285132272,20346958425,18271323186,9310455011,4053927535,14371004142,13627642999,
   1322237770,11841821356,12300435801,1029402865,12641575618,7744381127,7333216029,11479516198,
   1396916680,11574599225,2963745052,10115633136,5482996967,8501492971,6600530360,7381757502,
   6784097511,6934168235,6304435118,7086056244,5229694839,7610495121,3508692784,8140132980,
   1102015795,8170249179,1849552219,7130961788,4854657700,4598967669,6999454781,658955216,
   7140637960,3723257984,4506763211,6670574979,396782851,6170650712,5207012178,1743361989,
   6524122249,4042509705,2638056830,6386849164,3641694538,2524628289,6092203671,3977007281,
   1570621582,5554704044,4752690454,117043862,4476558551,5524598173,2424474667,2434595708,
   5638624052,5094621580,1195857704,3678886833,6722300363,6245139591,2403993893,3079913112,
   7859052638,9989091072,8596060916,4008317020,2555868977,9509356421,15392582613,19186196329,
   20410854655,19030164845,15277105451,9411540647,1570415049,8437084660,21145962912,37628868766,
   59426737198,88820134574,128770863942,183291621226,257517100492,358101891240,493542024204,
   674527429528,914538873412,1230206854186,1642020355078,2174857521324,2858570810724,
   3728705623780,4826919633224,6201563932052,7908032478434,10008844986172,12573714038820,
   15679104614074,19407510571588,23846443337886,29086764485286,35220686355084,42339318850008,
   50529575167630,59870808691386,70431082084734,82263044188672,95399839477478,109851046514922]
private def pvm_w0_7_p1 : List ℤ := pzig
  [125598723334560,142594018320732,160754430574448,179961798597268,200061427682914,
   220862457174808,242139427343252,263635280163604,285065823647930,306125423086258,
   326493870593194,345844336443616,363852001386200,380203036258420,394603715062812,
   406789246294840,416531853056778,423647838830082,428003388179602,429518752785496,
   428170621196932,423992664700296,417074237340346,407557220373430,395631188137490,
   381527188902318,365510393365592,347871880358904,328919942657236,308971315602900,
   288342639474482,267342425361896,246263818169322,225378408367934,204931226015876,
   185136971090348,166177518493010,148200698573838,131320267066850,115616911708242,
   101140136120836,87910869033974,75924625531892,65155021087984,55557449449884,47072774503072,
   39630916591318,33154224071852,27560533354148,22765851886612,18686637107396,15241670038272,
   12353531822524,9949698084986,7963279141714,6333449696156,5005619934882,3931397780106,
   3068385152094,2379846372752,1834285735134,1404970196406,1069428659130,808951568034,
   608106567288,454280415496,337254575834,248820340342,182437389098,132936904064,96267477922,
   69280043592,49547309548,35213425872,24870198746,17456616870,12178600758,8445866590,5822826642,
   3990662816,2718109110,1838972184,1234893598,822237754,542253870,353827776,228248278,145497476,
   91655312,57092422,35206016,21525620,13072722,7899066,4754740,2852736,1705592,1015190,600694,
   352806,205430,118514,67748,38418,21658,12170,6828,3834,2146,1196,662,350,176,80,32,8,0,0,0,0,
   0,0,0,0,0,0,0,0]
private def pvm_w0_7_p2 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_7_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_7_p4 : List ℤ := pzig
  [0]
private def pvm_w0_7 : List ℤ :=
  pvm_w0_7_p0 ++ (pvm_w0_7_p1 ++ (pvm_w0_7_p2 ++ (pvm_w0_7_p3 ++ pvm_w0_7_p4)))
private def pvm_w0_8_p0 : List ℤ := pzig
  [17743846,103568443,407673804,1246117643,3120468740,6550637561,11586464950,17069744553,
   20204889130,17451621349,7309381248,6467893620,15057082191,10971269832,3108930738,13519380585,
   8543328688,6472654922,12747060317,1687342180,11352138984,7201663265,7811424273,9844521302,
   4339411506,10609650361,1820774101,10479328760,402145682,10070180741,37871910,9648147274,
   340203234,9225195941,1396765577,8641923238,2980638554,7634170223,4853911547,5915336772,
   6615606346,3306394961,7678606709,83113279,7369876500,3680425038,5207533903,6416685021,
   1320538066,7012458884,3192076122,4667948399,6339711183,56185463,6114210882,4820373896,
   2053710787,6402627285,3519356479,3102972714,6264100390,2877392940,3308924213,6078849151,
   2967559533,2808338646,5864647906,3656790880,1615991961,5363506861,4620610159,236785495,
   4192845256,5332474872,2520516032,2044590485,5120373553,4693952001,1155790337,3181836614,
   5663624772,4849806124,1204695024,3341773027,6476792053,6675451835,3755492779,1110769942,
   6101941884,9370233186,9817547156,7179515450,2126149118,4211504661,10522812469,15679307911,
   18967105923,20010077405,18844430967,15631561111,10583742189,3824157543,4817865220,15757506192,
   29843574362,48388679234,73201166378,106819449002,152554887266,214726564802,298971758826,
   412435763436,564214595246,765773981470,1031328963504,1378457607244,1828628713302,
   2407720459462,3146704020380,4082173405420,5256814372422,6719920850658,8527650203136,
   10743081227746,13436159867444,16683244655330,20566272157464,25171648846590]
private def pvm_w0_8_p1 : List ℤ := pzig
  [30588636947712,36907221454490,44215626172168,52597360855842,62127781715212,72870408638166,
   84873051488572,98163755949622,112746850846712,128599322550658,145667576595396,163864817437928,
   183069351686550,203123914569274,223836101974910,244980114336610,266299890887086,
   287513532512130,308318956739824,328400735409746,347437880957294,365112255514574,
   381117345548192,395167116621674,407004541223404,416409405983612,423205116156628,
   427264232668510,428512452643164,426930836058188,422556228237238,415479889417722,
   405844364504062,393838720843792,379692405855166,363668023382498,346053319397968,
   327152691859320,307278586906452,286743137851662,265850339399806,244888992771982,
   224126631508322,203804599121100,184134372013762,165295137615546,147432586548326,
   130658849422940,115053472508198,100665279847312,87514938362224,75598041235852,64888538912742,
   55342356732262,46901043200866,39495306860604,33048328607780,27478770812484,22703432175974,
   18639515535074,15206491645728,12327560952982,9930735423684,7949577396722,6323638799562,
   4998644395000,3926461715890,3064900474604,2377384364770,1832535892320,1403709332004,
   1068499546802,808247527980,607558464648,453844722556,336903241652,248533731460,182200636208,
   132738736606,96100048620,69138564306,49429107596,35116700146,24792987642,17396323260,
   12132093182,8409924724,5794627318,3968085248,2699785312,1824133902,1223127664,813257338,
   535749994,349414966,225482044,143926546,90875542,56782180,35137452,21556240,13125926,7942040,
   4779366,2862024,1705556,1011098,595882,348822,202686,116858,66858,37978,21442,12046,6744,3764,
   2086,1146,618,320,156,70,24,6,0,0,0]
private def pvm_w0_8_p2 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_8_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_8_p4 : List ℤ := pzig
  [0]
private def pvm_w0_8 : List ℤ :=
  pvm_w0_8_p0 ++ (pvm_w0_8_p1 ++ (pvm_w0_8_p2 ++ (pvm_w0_8_p3 ++ pvm_w0_8_p4)))
private def pvm_w0_9_p0 : List ℤ := pzig
  [254410502,1160269177,3498301786,7942587903,14084963950,19370503437,19404444358,10972276637,
   3402853611,14259999274,11982045939,2072516477,13244322814,8235422451,7070359439,12284445546,
   144745958,11928826033,4836095748,9768396246,7652078837,7458519419,8912780360,5735718456,
   9247836183,4803427213,9061539624,4626018608,8525198579,5073218905,7637645290,5960143970,
   6297325059,7033827165,4381679716,7947690796,1843593573,8262929073,1175453809,7516585616,
   4244612392,5384634447,6622704953,1925545488,7407863216,2191362972,5914441339,5659003051,
   2204381708,6912370340,2506865356,4961882503,6005726305,353922856,6108622134,4484256692,
   2295777933,6286831063,3167195509,3333209410,6104195694,2408735730,3668508823,5913960817,
   2294018981,3442063328,5802866268,2776039230,2664018073,5626829429,3693032169,1274478004,
   5062274568,4704425516,696020710,3728713463,5252614397,2927992817,1424143586,4677450468,
   4713780880,1610129154,2490235859,5034901067,4488867967,1263680311,2778202678,5414305270,
   5231797476,2343185524,1912331617,5562519863,7001308881,5593874861,1783093769,3075929322,
   7386010376,9782105708,9498469902,6577482852,1632413022,4330655169,10198990693,15079975905,
   18329190213,19635807109,19002807235,16542449977,12437058869,6819166873,401994350,9528395776,
   21164057132,36339125396,56498866586,83631986180,120450832672,170477424798,238279079016,
   329779449158,452495436788,615910370906,831947552714,1115376287328,1484312735252,1960829837678,
   2571487498878,3347869646176]
private def pvm_w0_9_p1 : List ℤ := pzig
  [4327189815084,5552773587184,7074402734560,8948609427550,11238767139568,14014862870516,
   17353029062954,21334770948970,26045728876298,31574009818168,38008141671330,45434551244448,
   53934559339760,63581040508518,74434809978650,86540753676132,99923874631018,114585482216722,
   130499645215172,147610051855100,165827536261102,185028491201066,205054274879660,
   225711737660316,246775032064960,267988765564592,289072433149858,309726057291564,
   329636952173474,348487415786402,365963050106672,381761409146474,395600685308958,
   407228089326240,416427539558066,423026327229066,426900501699848,427978751545596,
   426244585552914,421736706723986,414547590150566,404820354023538,392744057215682,
   378547618928388,362492638284874,344865445378710,325968719167704,306112994017718,
   285608373742160,264756763695134,243844890396738,223138309826742,202876539503904,
   183269399322162,164494598518932,146696547767472,129986314269592,114442592466878,
   100113539800628,87019315681076,75155151817264,64494774693572,54994004964246,46594377217416,
   39226650498388,32814106055248,27275550641042,22527964481506,18488756257144,15077612250154,
   12217948657060,9837991295392,7871515642226,6258285215154,4944230303448,3881412284726,
   3027819838296,2347041148036,1807851047908,1383745624176,1052450719922,795425836280,
   597380833744,445818967720,330615778866,243639363532,178414045874,129826873888,93874768126,
   67449360004,48156223660,34165044428,24087142176,16876683924,11751943268,8133147284,5593791684,
   3822747378,2594952508,1748915984,1169617116,775662236,509769266,331815904,213825232,136384992,
   86106674,53826962,33334102,20465116,12465976,7539920,4531292,2706968,1607772,949306,557062,
   324746,188012,108084,61700,34984,19714,11048,6158,3410,1876,1010]
private def pvm_w0_9_p2 : List ℤ := pzig
  [532,270,126,54,18,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_9_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_9_p4 : List ℤ := pzig
  [0]
private def pvm_w0_9 : List ℤ :=
  pvm_w0_9_p0 ++ (pvm_w0_9_p1 ++ (pvm_w0_9_p2 ++ (pvm_w0_9_p3 ++ pvm_w0_9_p4)))
private def pvm_w0_10_p0 : List ℤ := pzig
  [1937684026,6509357891,13717315882,19925019083,18857058852,7273295737,8599871803,15187272938,
   5324716441,10136071367,11915299840,2565189154,12735753389,3262767126,11002214654,6739664363,
   8786396711,8444998404,7026086378,9049687309,6010681405,9001075592,5734873694,8507195263,
   6071854973,7602489102,6830714878,6225056385,7758629411,4294741874,8530359696,1796553319,
   8757237673,1131874883,8042533488,4127446366,6100187595,6584472787,2928432024,7749238112,
   1016669722,6967936931,4758993643,4062889970,6990016290,308353468,6583065427,4576782825,
   3318224502,6736393138,1571609666,5394186501,5583075735,936499608,6172178018,4093787988,
   2610537071,6206171503,2847917057,3523097852,5973999434,2092413510,3856864365,5760508805,
   1887759287,3741378680,5660008476,2210090056,3199017557,5600357551,2975142895,2166034828,
   5359050056,3994205514,582481167,4600551785,4902875935,1452766989,3004517882,5143942240,
   3521507364,522953715,4124108595,4847495277,2356725817,1605967102,4504767030,4564272076,
   1867193172,1936025261,4656390965,4777390095,2296632539,1480532878,4650765546,5642919834,
   4002265678,426514674,3594304625,6396886273,6885443429,4827890147,846701081,3794014488,
   7712702848,9811945646,9482361218,6761376152,2209539398,3345950919,8961457257,13797666933,
   17290464769,19115231605,19175042487,17578579803,14478741849,9979823631,4111498043,3294140186,
   12680621270,24763406152,40623924246,61827943394,90475329708,129335814968,182074002856,
   253432193538]
private def pvm_w0_10_p1 : List ℤ := pzig
  [349462618046,477887485980,648463084928,873347462326,1167587033164,1549656454960,2041961993128,
   2671388091988,3469899628288,4475072216842,5730529674516,7286340095466,9199282227740,
   11532864565506,14357108383972,17748086510510,21787096601262,26559402892992,32152584009568,
   38654471791206,46150613347798,54721286167050,64438174072770,75360763101718,87532507614874,
   100976918847238,115693780178370,131655643893732,148804756127116,167050624535814,
   186268455285520,206298610835812,226947192936876,247987866246944,269165007561374,
   290198163379970,310787713403114,330621610388640,349383030298342,366758681865016,
   382447450783520,396169041506986,407672292949864,416742835112966,423209744175880,
   426950892257336,427896767773364,426032616462158,421398808603774,414089404918396,
   404248987687126,392067918104792,377776245274560,361636530778248,343935888218262,
   324977572645710,305072470268516,284530821024410,263654466463584,242729871989398,
   222022130270844,201770101912476,182182785094498,163436937142322,145675912088310,
   129009634374346,113515594427304,99240721065362,86203960306710,74399376801860,63799596104062,
   54359419576380,46019462019396,38709681130046,32352688381228,26866754981440,22168453875268,
   18174905855808,14805620888296,11983943083610,9638120463638,7702030678114,6115602080268,
   4824975481558,3782454428764,2946290683202,2280347611984,1753678929902,1340054907312,
   1017463272532,767607435240,575420018476,428604939802,317216691800,233281464578,170461647914,
   123763114972,89283354188,63997707532,45580453174,32257110792,22684125662,15852030022,
   11008311336,7596519710,5208567462,3547642544,2399607562,1611150654,1073276518,708983606,
   464181464,301076542,193405402,123026656,77497162,48353316,29894410,18323112,11140444,6722728,
   4028468,2397948,1418186,833364,486532,282162,162532]
private def pvm_w0_10_p2 : List ℤ := pzig
  [92984,52840,29832,16738,9332,5164,2828,1532,814,416,206,92,36,12,2,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0]
private def pvm_w0_10_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_10_p4 : List ℤ := pzig
  [0]
private def pvm_w0_10 : List ℤ :=
  pvm_w0_10_p0 ++ (pvm_w0_10_p1 ++ (pvm_w0_10_p2 ++ (pvm_w0_10_p3 ++ pvm_w0_10_p4)))
private def pvm_w0_11_p0 : List ℤ := pzig
  [8069432922,17825586481,21115303716,10345605699,8027551377,15370893214,2994255725,12400796507,
   8681489720,8187052090,10928530265,4866824171,11494390264,2833106248,11385615433,1960824979,
   11044798082,2034289076,10574973287,2852016903,9889326800,4214678080,8808219151,5879828387,
   7138204222,7521963420,4755126277,8723436135,1695200702,9017858308,1762674566,7999549559,
   5060507709,5492077740,7420337862,1733039617,8039769863,2511734705,6419878134,6020232868,
   2736072459,7463548537,1938160185,6009032360,5792694488,1955999171,6966561243,3005440489,
   4600362798,6318698774,301243108,5913130779,4959280405,1759590616,6275558738,3548238262,
   3081493919,6143254967,2443446649,3784833964,5865713598,1784564960,4027285999,5644348821,
   1596880743,3913785090,5544680018,1859915552,3469252639,5513666703,2523530633,2645622584,
   5394898742,3468490940,1358605725,4947914271,4447945577,405470875,3877305606,5072080090,
   2425912546,1965364659,4832320557,4179475589,634267273,3273440396,4891993296,3237158986,
   463175153,3802702053,4716993675,2724566599,860638536,3909860698,4704040250,2837844700,
   592202239,3738105737,4994089255,3723959869,566392851,2972077930,5300032042,5374043268,
   3122641248,553831311,4262134797,6643800385,6809589427,4657276795,824373565,3615164178,
   7446301922,9649240268,9681344940,7505240762,3506110394,1602433241,6988731617,11910783355,
   15781818321,18218282181,19084864829,18416927887,16314945995,12909657789,8290214273,2390967123]
private def pvm_w0_11_p1 : List ℤ := pzig
  [5046090400,14490854068,26716938916,42882732248,64573742816,93914795862,133747864298,
   187790268462,260823929362,358987611384,490108051564,664031244342,893030033850,1192300664816,
   1580467450722,2080092080026,2718241977290,3527076314746,4544364025370,5813932914800,
   7386061169146,9317729684630,11672644846244,14521019309486,17939092635954,22008302251162,
   26814031589306,32443939580734,38985877817858,46525358997204,55142574153634,64909038261912,
   75883963173520,88110433891188,101611496469148,116386338427982,132406763621494,149614133532242,
   167916944440190,187189241838764,207270068822620,227964084100198,249043426610330,
   270250877982008,291304338329816,311902551314818,331731924651450,350474236700574,
   367814987864612,383452110969268,397104700674642,408521395772046,417488064817440,
   423834480206890,427439696450762,428235886314300,426210455072188,421406344295070,
   413920526763288,403900768407678,391540799874944,377074110439114,360766643878996,
   342908721822464,323806536937554,303773554625444,283122148853826,262155776168488,
   241161954509014,220406257762440,200127471066182,180533987431506,161801468941628,
   144071743684734,127452859919974,112020173955830,97818313928754,84863842356200,73148434870438,
   62642396229106,53298343736524,45054901985556,37840272483332,31575567171466,26177823486274,
   21562646575652,17646448789236,14348276954100,11591235095560,9303524982858,7419139027120,
   5878248755164,4627336634658,3619119624590,2812310517426,2171259251616,1665511881400,
   1269320185528,961129963926,723070842056,540465018820,401367208446,296143455746,217092828584,
   158113267324,114410961424,82251305444,58748560934,41690698588,29395478498,20593645656,
   14335169896,9914713138,6812900656,4650435608,3152561008,2121797980,1417252900,939088932,
   617009772,401816200,259279708,165736076,104937598,65815742,40896950,25185036,15376220]
private def pvm_w0_11_p2 : List ℤ := pzig
  [9310958,5594452,3336568,1975812,1161930,678652,393680,226824,129802,73772,41654,23356,13006,
   7192,3942,2128,1132,592,294,138,58,18,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_11_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_11_p4 : List ℤ := pzig
  [0]
private def pvm_w0_11 : List ℤ :=
  pvm_w0_11_p0 ++ (pvm_w0_11_p1 ++ (pvm_w0_11_p2 ++ (pvm_w0_11_p3 ++ pvm_w0_11_p4)))
private def pvm_w0_12_p0 : List ℤ := pzig
  [18895170374,21092703599,2326699874,15462721762,8171259501,11070604155,9912399462,8517555266,
   10144971447,7418655831,9696654538,7365725410,8772367047,8002666433,7335580738,8976443328,
   5288841515,9891378889,2595171424,10303508312,623308980,9772024575,4017318091,7970308392,
   7003380858,4835981291,8852694299,709314086,8891724718,3616352454,6785709751,7011073499,
   2815030136,8330925378,1997994122,6896857385,6058566239,2960249638,7728960594,2108446906,
   6102183373,6155800063,1681393496,7156531086,3503739236,4386210915,6679018875,817251581,
   5862355550,5420211690,1352436615,6382810961,3983590547,2851748464,6333138168,2735211922,
   3746843297,6045341339,1845623483,4178311218,5740076756,1368572238,4274626563,5528771549,
   1300878673,4105265286,5441682996,1606352850,3664151547,5439891149,2233187719,2904778362,
   5387899926,3117604134,1778828737,5076413885,4095609235,237780368,4290358490,4858023706,
   1627696450,2805813007,5025588013,3461594085,592009710,4150916124,4702028994,1969197906,
   2038949359,4603811787,4085560167,921721187,2754373490,4635029968,3644548252,463518480,
   2939625001,4573239687,3584268587,593165103,2718080104,4548171564,3978487200,1355378836,
   1997950337,4432169375,4783113433,2911170705,348477036,3605119158,5479430738,5191102086,
   2838898324,740380399,4301788585,6611531177,6888184015,5017157915,1488105781,2773696388,
   6664383962,9232218746,9891563938,8469223658,5199697598,649793046,4467070509,9455317391]
private def pvm_w0_12_p1 : List ℤ := pzig
  [13712970267,16803263583,18509147271,18789296155,17697798813,15347809433,11859999639,
   7266315631,1450395689,5869122014,15194090580,27331907728,43448683178,65129750662,94509902486,
   134435703214,188622008858,261856954040,360291186622,491763171532,666140824742,895730964288,
   1195768906800,1584933519956,2085868888560,2725744916032,3536843233002,4557098510752,
   5830557489630,7407757463238,9345984586634,11709324603046,14568446689900,18000101716594,
   22086292761780,26913041628114,32568704849418,39141846250188,46718679119620,55380076189578,
   65198177324674,76232688883788,88527000186224,102104239174740,116963405930344,133075770277132,
   150381748768140,168788460891638,188168138457534,208357556483666,229158646163978,
   250340405897330,271642153745700,292778100032064,313443170826314,333319957759646,
   352086594701838,369425288954170,385031189597566,398621256535452,409942781656200,
   418781204568378,424966876357626,428380468458976,428956791134712,426686858769008,
   421618110708276,413852773949214,403544441916970,390893032260996,376138360426946,
   359552617723906,341432077144892,322088373125952,301839711026092,281002351618438,
   259882682672498,238770139560192,217931179222366,197604452677892,177997260956096,
   159283317127730,141601775724398,125057436412118,109721986822672,95636121385488,82812356596240,
   71238355589218,60880575210414,51688057701266,43596206815860,36530412885388,30409419520918,
   25148352834168,20661360248392,16863829743420,13674181933390,11015246531822,8815250682072,
   7008458343940,5535507004190,4343490856352,3385839323668,2622037512862,2017231680146,
   1541758427450,1170631252624,883012400000,661692012692,492590819912,364297429198,267647007796,
   195344789808,141635330254,102016563768,72996349570,51888191802,36642168016,25706758856,
   17917222632,12406350080,8533796148,5830638172,3956286258,2665322942,1782250978,1182475292,
   778141150]
private def pvm_w0_12_p2 : List ℤ := pzig
  [507704588,328330512,210401958,133584764,84024932,52363102,32335058,19790380,12008618,7226508,
   4314170,2555790,1502830,877270,508454,292616,167224,94898,53486,29932,16632,9170,5006,2702,
   1440,750,376,176,76,26,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_12_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_12_p4 : List ℤ := pzig
  [0]
private def pvm_w0_12 : List ℤ :=
  pvm_w0_12_p0 ++ (pvm_w0_12_p1 ++ (pvm_w0_12_p2 ++ (pvm_w0_12_p3 ++ pvm_w0_12_p4)))
private def pvm_w0_13_p0 : List ℤ := pzig
  [25625953388,2047582929,17480234565,514938592,14832406534,1656227438,13065632089,4199730431,
   11162236530,6849303342,8610972353,9191276117,5186942094,10669641636,996575719,10698060435,
   3464055623,8863780646,7342508546,5171117969,9618055261,224749346,9446617260,4770508636,
   6575606279,8284179481,1655225544,8996122746,3758284550,6430036819,7637619369,1389637242,
   8297913560,4114177922,5284061197,7590109623,143028741,7257426760,5341753960,3148088261,
   7512512507,2590291027,5318248260,6633848768,45905656,6413301551,5227673435,1949917646,
   6713056860,3750037862,3327717675,6543026545,2475613271,4167639058,6173312434,1536036662,
   4600837081,5789234873,968255801,4739599518,5505480772,752687586,4647621933,5370531873,
   864621743,4361231008,5352015780,1296538744,3877612773,5384019449,1996096587,3120097276,
   5376957098,2884848284,2037782599,5140344133,3862125949,610545058,4491680894,4675342284,
   1129555270,3255068915,5028365011,2920670485,1344632808,4546017456,4358762128,1019652308,
   2974805463,4817209721,3311488091,425518782,3805340596,4611011306,2426139984,1265827439,
   4101655191,4343511905,1945071485,1563047666,4100322736,4227055950,1938469420,1397107533,
   3921992869,4314069529,2408930613,755611242,3528151644,4541813828,3339833476,506730768,
   2626663255,4621653035,4606155233,2592458309,604048184,3702749334,5476436874,5244183118,
   3069612454,333778723,3853172985,6347156285,7031996607,5682172741,2619613965,1399909248]
private def pvm_w0_13_p1 : List ℤ := pzig
  [5392482940,8428068274,9847492756,9342990098,6973728894,3132895352,1578971751,6514224693,
   11076156037,14777595457,17302990061,18523659505,18440810737,17125999711,14690038043,
   11229551321,6747446173,1104775513,5999649844,15079682574,26939869986,42737818186,64049344798,
   92987759118,132368277416,185881074742,258293329888,355723624058,485977561518,658910470038,
   886830883348,1184977579376,1572054450744,2070780785050,2708449856538,3517507306910,
   4536119542072,5808669182542,7386136795564,9326350634300,11694058990328,14560746257904,
   18004127624484,22107290335878,26957448645730,32644259910074,39257662959452,46885246316386,
   55609185857220,65502796262194,76626755621280,89025108976906,102721204988440,117713738879732,
   133973076724530,151438050179726,170013433686418,189568317677996,209935559953452,
   230912453798236,252262714483330,273719846261722,294991890989658,315767479340662,
   335723028381834,354530869214688,371868038766702,387425420127938,400916871409838,
   412087960788450,420723933704050,426656569504220,429769627579086,430002635682220,
   427352842227066,421875241659134,413680678008288,402932122743436,389839301936608,
   374651915586636,357651750597258,339144034518414,319448402169506,298889847394464,
   277790010262400,256459112863774,235188809656438,214246162456314,193868885905074,
   174261939517342,155595473422262,138004073274084,121587199285670,106410675259664,
   92509054701826,79888672235258,68531180471822,58397376015734,49431132509334,41563280808638,
   34715302939812,28802734535206,23738198383390,19434018877160,15804392911042,12767116145032,
   10244883220886,8166195480314,6465919730368,5085547151248,3973203503546,3083461309440,
   2377002314278,1820174655088,1384484040914,1046052228226,785069628926,585262552116,
   433389812804,318778517674,232904838192,169022429400,121838709574,87237354290,62043987572,
   43831124694,30757898170,21439931118]
private def pvm_w0_13_p2 : List ℤ := pzig
  [14844844832,10209211782,6973207252,4729698266,3184984806,2128847344,1411944090,928942778,
   606067686,391999982,251290126,159627900,100470688,62655110,38715546,23707368,14389072,8658316,
   5166476,3057886,1795616,1046304,605098,347354,197946,111992,62904,35076,19410,10648,5792,3118,
   1654,852,428,204,90,32,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0]
private def pvm_w0_13_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_13_p4 : List ℤ := pzig
  [0]
private def pvm_w0_13 : List ℤ :=
  pvm_w0_13_p0 ++ (pvm_w0_13_p1 ++ (pvm_w0_13_p2 ++ (pvm_w0_13_p3 ++ pvm_w0_13_p4)))
private def pvm_w0_14_p0 : List ℤ := pzig
  [20680214046,18784154694,881633633,15398680529,8289052031,8780427474,12348620432,1165412673,
   12100411323,5700121857,8204759922,10136361464,1947076095,10887779059,4651216629,7690007254,
   9253105576,1656180747,10034557915,4863312395,6571744730,9084027912,288192285,9028656811,
   5940822039,4632812310,9045395870,1960775028,7371039443,7294181369,1765255806,8403024876,
   4638105874,4614017977,8066273881,1817220883,6397821322,6863170658,684305819,7223540679,
   5270292327,2638290974,7339982830,3646219080,4007472193,7022044447,2215439699,4867618284,
   6503475236,1092326610,5339293835,5956797523,309506311,5532115864,5503546702,152835463,
   5524897393,5207492405,313669850,5386019598,5065939332,178683911,5140889929,5070656115,
   210540143,4747098490,5192432118,836544020,4182789765,5324053445,1686736611,3383342068,
   5380208430,2666996440,2276517363,5201913437,3694878173,866973970,4623074066,4553845454,
   824247410,3507998821,5000523251,2575880975,1778058394,4717636026,4075147358,415443812,
   3482674489,4800476417,2686871581,1286791550,4308181258,4322477318,1422778210,2368772815,
   4550839053,3750757315,564131421,2914545658,4524285654,3353133020,181376362,3049022941,
   4435556321,3247271379,246554319,2851441720,4343304116,3456698400,737907142,2335067495,
   4187061239,3911069519,1675158615,1388968456,3795250766,4437288010,3041845022,235368836,
   2745248257,4615156515,4601632187,2708419147,346237618,3413272170,5348247784,5445263634]
private def pvm_w0_14_p1 : List ℤ := pzig
  [3652347078,524420428,2977886809,5784215359,7053082029,6409148813,3988357259,353348127,
   3655149472,7133053800,9340764936,9838126982,8512971118,5564710078,1447093324,3253013223,
   7948610079,12130104371,15404016991,17529646327,18426464253,18126058169,16710770503,
   14278050999,10904030127,6581494533,1163359167,5665276032,14420125016,25885476326,41195268224,
   61909074810,90112953054,128575164064,180941462800,251950333818,347689783528,475924998688,
   646487217126,871699213454,1166843350262,1550692448468,2046091894904,2680554534918,
   3486845002280,4503548234440,5775596127734,7354693005166,9299579983118,11676098794422,
   14557013936008,18021527609440,22154414996190,27044731977494,32784072598434,39464357088456,
   47175133628886,56000405851534,66015044537872,77280876787924,89842563320042,103723396268616,
   118921187550118,135404454093712,153109119221306,171935941426684,191748870436566,
   212374520307816,233602925542528,255189696544408,276859622722402,298311702318762,
   319225513860696,339268777676494,358105882352694,375407079456980,390857995862054,
   404169083599910,415084617631684,423390856284196,428922999523232,431570623852944,
   431281341356070,428062516537106,421980966817334,413160663936498,401778543191240,
   388058614651792,372264649738028,354691778944776,335657375585640,315491615637132,
   294528098775864,273094893946200,251506335226504,230055840541454,209009959382164,
   188603781980030,169037768514894,150475988501928,133045700195804,116838148537406,
   101910418735208,88288152733260,75968919317182,64926025831114,55112568795536,46465539089262,
   38909821605878,32361957018526,26733562962800,21934342377806,17874636516004,14467507536730,
   11630359021498,9286121172386,7364040680834,5800123778150,4537285597982,3525260446452,
   2720326445006,2084894695972,1587008044810,1199788204592,900863093934,671799342420,
   497558529364,365990137956]
private def pvm_w0_14_p2 : List ℤ := pzig
  [267369524432,193985384508,139778150610,100028379448,71092421586,50181448484,35179196814,
   24493501970,16936744946,11630627106,7931120954,5369941564,3609386200,2407865786,1593885864,
   1046620730,681564968,440043078,281611730,178604262,112243662,69892830,43122634,26363802,
   15973234,9592454,5710846,3371256,1973744,1146252,660436,377586,214236,120632,67408,37380,
   20572,11224,6060,3238,1704,874,438,206,88,34,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_14_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_14_p4 : List ℤ := pzig
  [0]
private def pvm_w0_14 : List ℤ :=
  pvm_w0_14_p0 ++ (pvm_w0_14_p1 ++ (pvm_w0_14_p2 ++ (pvm_w0_14_p3 ++ pvm_w0_14_p4)))
private def pvm_w0_15_p0 : List ℤ := pzig
  [10152435488,18870721832,18939531190,7173135414,8377121033,14421269777,5873595751,7889959286,
   12271113290,3063118922,8999899159,10365472343,70087444,10003768734,8094985540,3069941041,
   10341110167,5451997939,5596917566,9883941860,2662132536,7435819569,8736503223,1737674,
   8515726278,7118779712,2318730501,8891877623,5279942981,4160633146,8703367218,3440152998,
   5492728255,8126329727,1760789821,6352458848,7335677704,338539152,6821476883,6479504463,
   783528948,7001472090,5666319446,1599071069,6992235415,4970299115,2131127838,6867042064,
   4447232488,2421950931,6673419291,4121056817,2492283790,6461229078,3973935514,2345549167,
   6243358527,4007064523,2015699538,5982067170,4206149686,1493974839,5669333593,4503155797,
   768579862,5238183714,4868717786,127731046,4620211949,5193989033,1202474011,3765704506,
   5379278308,2359596806,2596372427,5284572129,3514930529,1134324734,4761313140,4461792518,
   586809654,3697660061,4989856411,2354116419,2050784022,4813512102,3889974284,54359512,
   3762627801,4747321573,2272876811,1793586062,4532478448,4041913846,745214930,3005207027,
   4660365409,3175617689,394133220,3655616332,4498310256,2462123700,1083945685,3906630521,
   4292778641,2067733385,1353923702,3915524106,4166493302,2029623532,1228435665,3750961217,
   4165693907,2319872047,735802480,3372585264,4230749456,2907186978,127924110,2693238625,
   4193299443,3680660869,1417929161,1522800604,3790905262,4391019126,3080159300,413697010]
private def pvm_w0_15_p1 : List ℤ := pzig
  [2503626005,4477532035,4720051711,3135705139,299391731,2782854774,5024907334,5639663894,
   4402434034,1681278652,1726359345,4839492183,6767213525,6960463033,5343770343,2282692077,
   1547165664,5321321562,8248766382,9746865144,9537626388,7645378210,4347834550,111271282,
   4505685045,8965476523,12828110701,15775272017,17617693905,18298489215,17865974631,16414933833,
   14034701591,10779294281,6632392305,1453639361,5070320482,13458813224,24481543632,39237415948,
   59254881366,86599887016,124011068208,175089013686,244536367338,338432158234,464548035474,
   632730794318,855354832810,1147824008428,1529110621804,2022338133598,2655404732882,
   3461615639438,4480281437722,5757252332328,7345360883512,9304723800448,11702832544804,
   14614366629754,18120679181568,22308905865628,27270638666600,33100110836066,39891867551102,
   47737929650448,56724478598284,66928108309202,78411721686354,91220195798840,105375980445158,
   120874818503656,137681790666288,155727903394504,174907453337038,195076398554502,
   216051938999668,237613463767748,259504972087286,281439019737480,303102175111296,
   324161887445870,344274583669458,363094733580692,380284561938126,395524038366382,
   408520740060000,419019163267512,426809066058642,431732460484128,433688932134194,
   432639040901230,428605643021296,421673069823986,411984201230344,399735575543232,
   385170771602282,368572376343710,350252906434060,330545087164696,309791906038104,
   288336851782678,266514720820274,244643323644540,223016357854284,201897639655102,
   181516808044376,162066540153810,143701245140902,126537140075236,110653557477168,
   96095293658346,82875781767930,70980863412718,60372935982838,50995266589982,42776285175106,
   35633696793518,29478284582454,24217308578860,19757439187764,16007195451558,12878885506740,
   10290068695706,8164575516558,6433133307708,5033652868138,3911234671764]
private def pvm_w0_15_p2 : List ℤ := pzig
  [3017953436022,2312477039020,1759570738004,1329531040604,997586188584,743292734608,
   549950654558,404053156078,294781946366,213554211344,153623886242,109736906958,77837965330,
   54824797146,38345133180,26631047742,18365433746,12575600336,8549423670,5769995784,3865251604,
   2569571660,1694838228,1108856784,719439890,462786836,295080352,186463240,116756372,72437914,
   44528344,27120820,16368018,9789600,5803226,3410186,1986868,1147920,657766,373868,210808,
   117930,65452,36032,19674,10646,5702,3014,1568,796,390,178,76,28,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_15_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_15_p4 : List ℤ := pzig
  [0]
private def pvm_w0_15 : List ℤ :=
  pvm_w0_15_p0 ++ (pvm_w0_15_p1 ++ (pvm_w0_15_p2 ++ (pvm_w0_15_p3 ++ pvm_w0_15_p4)))
private def pvm_w0_16_p0 : List ℤ := pzig
  [3083110604,8576220778,15202899736,18919329030,15628474306,5063136214,7370815661,13560457293,
   9089147519,2317432028,11073175350,9720819648,273394939,9587017015,9580375889,481264389,
   8788289424,9250825716,645967262,8368321143,8865465121,531426365,8134244676,8457605096,
   295749242,7974295781,8042683237,30262367,7826847136,7635787226,207694963,7660744373,
   7253807257,382234936,7460835442,6916112684,474609235,7217978205,6641270255,473677016,
   6932639868,6432561426,360412459,6616701291,6282371411,125847366,6258763376,6203689110,
   211734620,5831474489,6188298367,666131701,5342207390,6191074012,1243187504,4754945985,
   6207072327,1906317635,4034354610,6173315830,2665318620,3176611133,6033477395,3453639049,
   2130015646,5729359110,4227755180,926964249,5166488649,4885964873,437216731,4304127254,
   5316688734,1856320314,3074125643,5380246821,3232207129,1516730718,4946870020,4343975782,
   301405892,3913750675,4991585865,2159473605,2288289644,4904751390,3763556424,191862427,
   3948922517,4720208689,2016024549,2103149886,4649104622,3848254054,334176392,3363815503,
   4670612647,2759895027,991065806,4030040118,4348579870,1795581628,1885621419,4295630507,
   3945187621,1120774449,2367027330,4347463240,3651883616,780123672,2507168693,4283296271,
   3555078457,798941247,2364247366,4156052622,3638792142,1156051940,1918076533,3936504507,
   3864468143,1800531563,1150702564,3498511600,4100076948,2690580654,12861595,2699364605]
private def pvm_w0_16_p1 : List ℤ := pzig
  [4123355587,3661495959,1540244829,1293920422,3599758162,4393755326,3357692768,919324994,
   1960605035,4165237355,4843355459,3728957201,1212938535,1841923578,4415058018,5651379758,
   5125718286,2969582648,199516145,3498444435,6033428111,7120760765,6450959015,4154478609,
   735165785,3086605390,6541266170,8954461162,9869255674,9119798370,6823163200,3309051666,
   961157119,5469225425,9721212741,13321729723,16007159521,17636432819,18171302423,17658640535,
   16196710271,13881438733,10758028391,6792079971,1841162473,4391812262,12413652516,22990901316,
   37208577366,56562552576,83088425076,119513842640,169437655224,237558921254,329969108694,
   454498795542,621110785896,842350156902,1133864383832,1514985790530,2009352468582,
   2645549679434,3457762096616,4486414898262,5778757581436,7389333770924,9380286452162,
   11821450087506,14790167762450,18370757948754,22653560169680,27733508130530,33708195135680,
   40675405168592,48730097906272,57960868784318,68445948895048,80248848275196,93413775732390,
   107960998012868,123882337035334,141137038014284,159648259461092,179300433409136,
   199937727403200,221363815197358,243343127591848,265603700476386,287841662596686,
   309727319637098,330912705198972,351040388272370,369753250205986,386704873049668,
   401570122920064,414055476940982,423908636104618,430926987642736,434964524378742,
   435936892129876,433824319291342,428672283873980,420589886403000,409746012161332,
   396363473363266,380711414576444,363096340088222,343852177778054,323329827278496,
   301886647486700,279876318763606,257639471119924,235495407018474,213735172577718,
   192616149388912,172358255099256,153141758357418,135106637187958,118353344126958,
   102944790384646,88909326821490,76244481394354,64921209244632,54888420552294,46077570548366,
   38407123638294,31786737195240,26121047578824]
private def pvm_w0_16_p2 : List ℤ := pzig
  [21312978432222,17266526644870,13889012563840,11092807003716,8796568019470,6926035429430,
   5414441051074,4202597953134,3238733208700,2478126269210,1882609955856,1419984082784,
   1063383787450,790636516758,583633866076,427737432318,311231685420,224831638548,161248803366,
   114815527132,81165278640,56964711720,39692291934,27457800210,18856991518,12855953312,
   8700160784,5843773090,3895291852,2576269342,1690285540,1099897074,709692488,453962788,
   287816470,180834922,112580304,69441130,42435164,25691506,15410832,9159438,5394660,3148954,
   1821954,1045050,594336,335172,187446,103970,57190,31194,16864,9030,4778,2492,1274,634,300,134,
   54,18,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_16_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_16_p4 : List ℤ := pzig
  [0]
private def pvm_w0_16 : List ℤ :=
  pvm_w0_16_p0 ++ (pvm_w0_16_p1 ++ (pvm_w0_16_p2 ++ (pvm_w0_16_p3 ++ pvm_w0_16_p4)))
private def pvm_w0_17_p0 : List ℤ := pzig
  [585951312,2160190804,5330338344,10041375562,15026238672,17833634536,15925506218,8528364352,
   1992511375,10655793981,12616305669,6629498033,3412828596,10603595848,9816954116,1716520888,
   7424882387,10431509209,4970376065,4406217784,9895254292,6946723666,1827742107,8846222387,
   8074128909,305422829,7575239008,8622726116,2048459204,6217574347,8764661573,3456927931,
   4834490170,8611391494,4580122108,3462282991,8222582213,5469823557,2130880824,7634092250,
   6150969710,836148329,6894582151,6619587391,422894713,6011951334,6904344832,1610641178,
   4982644995,6992583599,2737949937,3842290952,6859607632,3765654064,2569499429,6509837997,
   4656985417,1208235578,5887005702,5372660854,227078778,5003826133,5827272823,1668846443,
   3818289316,5969336812,3040702968,2380042803,5696522671,4220664733,713474982,4973205202,
   5074712518,1038280886,3754350989,5436697619,2737729389,2100877612,5186350476,4125692860,
   138410729,4218232469,4973820603,1890835325,2587598752,5020646326,3632221698,443830689,
   4129714301,4712897451,1826956769,2340547242,4748189322,3724120758,71193138,3585483673,
   4678997807,2503786421,1358016322,4235447302,4215128596,1368756150,2355082887,4473897371,
   3640535493,471933057,2954088796,4468746124,3157536594,104155191,3253882703,4375679659,
   2852629059,346751110,3304033460,4293630390,2786812202,285710629,3147918913,4218708053,
   2953642021,91946371,2782012512,4129972764,3287085596,753484296,2136041243,3914457713]
private def pvm_w0_17_p1 : List ℤ := pzig
  [3710665423,1667672115,1169153992,3417099284,4030597774,2753315206,197999846,2453209439,
   4004729799,3789264383,1925124485,785793536,3213525394,4358945150,3755576906,1643035832,
   1164507025,3619690815,4823254477,4325683967,2274831837,648209084,3486747304,5336726066,
   5613250148,4199839748,1469174754,1835632859,4831113605,6742192293,7081064861,5734603655,
   2971843109,631941440,4346383792,7457618506,9398823634,9826083882,8655076420,6055285958,
   2390057732,1876457595,6262709869,10327072835,13712830101,16183662627,17630676465,18045294985,
   17481070981,16024151321,13764348067,10753163873,6957040411,2222290573,3753014182,11461332628,
   21650272230,35399619234,54208155944,80107765064,115822999110,164976063412,232330002858,
   324077115568,448191268532,614852889844,836938307726,1130563864748,1515686034360,2016758559682,
   2663429719090,3491245383588,4542321217984,5865950702938,7519107114784,9566777998882,
   12082057379958,15145923257156,18846636038540,23278695048974,28541288541752,34736182168468,
   41965017509104,50326026733080,59910200804256,70796978021708,83049556352826,96709979500390,
   111794193308600,128287304056312,146139290622028,165261433531630,185523727838126,
   206753537478838,228735717510762,251214375669946,273896372823156,296456581326582,
   318544834269928,339794406570196,359831773292558,378287300117840,394806446915166,
   409061015637228,420759949985370,429659195469826,435570155021286,438366329371338,
   437987813457512,434443425567350,427810365727858,418231423899380,405909878948854,
   391102340682016,374109884411966,355267904660508,334935165467782,313482545406186,
   291281965594268,268695952201500,246068226313900,223715638826710,201921681061028,
   180931708094520,160949917219588,142138034952580,124615588518974,108461575894080]
private def pvm_w0_17_p2 : List ℤ := pzig
  [93717304174954,80390139294090,68457899775120,57873631839366,48570520874122,40466722752926,
   33469934797012,27481566843816,22400414481504,18125776073664,14559990642718,11610403798292,
   9190793157104,7222302987382,5633950244658,4362771065768,3353678702198,2559101604846,
   1938464922738,1457571129010,1087926849136,806054063952,592815286554,432774440172,313608206130,
   225576669540,161057209170,114141749282,80294669252,56066759072,38859485526,26733342390,
   18254037258,12370567880,8319740226,5552280300,3676326918,2414717354,1573066926,1016179354,
   650800148,413136446,259913796,162026926,100072040,61230452,37113292,22284012,13254688,7810560,
   4560016,2637950,1512286,859248,483914,270166,149532,82056,44630,24058,12844,6782,3532,1806,
   906,436,200,84,30,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_17_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_17_p4 : List ℤ := pzig
  [0]
private def pvm_w0_17 : List ℤ :=
  pvm_w0_17_p0 ++ (pvm_w0_17_p1 ++ (pvm_w0_17_p2 ++ (pvm_w0_17_p3 ++ pvm_w0_17_p4)))
private def pvm_w0_18_p0 : List ℤ := pzig
  [70180506,321585986,1007170436,2478040120,5049588562,8728281778,12902634286,16224474152,
   16928192068,13650150270,6444715962,2637568921,10030564667,12290564387,8161295351,237314256,
   8165641842,10884437556,6693780780,1714817765,8750614463,9641959619,3772276787,4640058378,
   9538320124,7322904946,279930763,7538021435,8926443951,3436523021,4598996014,8911013170,
   6137039038,1424612569,7703375389,7722181063,1541418837,5746244212,8240916604,4018209954,
   3387722443,7869421635,5828711151,920635992,6773554422,6940023638,1401198564,5151017271,
   7324536043,3430973755,3202644954,7042689910,5003624932,1090313517,6156517421,6056473375,
   986757151,4768242578,6495665202,2890051276,2998882507,6320335847,4430939785,1000564650,
   5506925532,5487679150,1050538676,4141579071,5909163691,2935351105,2306840962,5628072352,
   4442711550,220007143,4615682837,5325919959,1891713391,2947842602,5432559790,3696510378,
   832040041,4641015945,4876240477,1438187023,3026386660,5157207826,3419728432,807143733,
   4368769395,4690753171,1601895521,2600497244,4866466058,3622671912,163061641,3776175309,
   4699159935,2337813831,1609274104,4389906060,4137453208,1096069202,2639994823,4571182363,
   3447855415,70247815,3303138530,4494203130,2794288878,660426371,3660685169,4331712715,
   2303722347,1109737212,3799827526,4168583640,2043760470,1269703007,3796581803,4079870707,
   2014553193,1164629068,3647926396,4068585228,2233949294,800815785,3357641213,4081518603]
private def pvm_w0_18_p1 : List ℤ := pzig
  [2641555011,159866072,2848168288,4046136628,3175762312,725404692,2051838889,3798089517,
   3697879259,1830714235,893799006,3186604344,4000052068,2996889022,654112088,1987802797,
   3783318051,3967000171,2471119257,71187562,2623858770,4177749734,4126710082,2477813104,
   161898261,2825697591,4558061475,4750280587,3320136625,712852637,2251484514,4643941072,
   5724287844,5156867426,3077168256,24006904,3215522221,5813156057,7114479657,6793659563,
   4900813799,1814791801,1857002168,5408257564,8179095354,9682430828,9671391008,8143082036,
   5305987076,1529358298,2727365187,6998133115,10879053687,14062614793,16346678665,17635488363,
   17930902229,17302964773,15845817531,13638671611,10718473245,7051110787,2490787925,3265762732,
   10722119916,20631216932,34069092028,52540377780,78109957230,113561431764,162598042064,
   230102687210,322460053274,447936195494,617118878026,843430702210,1143720367868,1538921002596,
   2054755894304,2722474584242,3579601697602,4670666608598,6047862113660,7771569312304,
   9910685296234,12542688430636,15753366265198,19636121552720,24290774888896,29821799531426,
   36335945719458,43939232089510,52733305566666,62811207075816,74252628722762,87118799178708,
   101447178726484,117246182997198,134490188780094,153115105743412,173014816171798,
   194038781586412,215991087808380,238631153014338,261676261404442,284806008730102,
   307668653554888,329889262140638,351079424073782,370848211757034,388813968507490,
   404616441475436,417928729424504,428468495659668,436007908505772,440381819054062,
   441493766492970,439319508328802,433907897345764,425379061284904,413919978139518,
   399777672497032,383250377837382,364677106896998,344426139730368,322882973315488,
   300438277716686,277476374711464]
private def pvm_w0_18_p2 : List ℤ := pzig
  [254364699187410,231444625811760,209023948730946,187371197108260,166711862050782,
   147226508794900,129050658406534,112276250024580,96954440039130,83099459239080,70693232617190,
   59690468142864,50023938459540,41609710169512,34352115326406,28148304806956,22892269495746,
   18478259537796,14803572055488,11770712254408,9288960930760,7275402641222,5655483175990,
   4363172836814,3340814095710,2538729548858,1914659918512,1433093430842,1064538311332,
   784780258188,574157205380,416874889108,300378948484,214792674232,152424138642,107342290024,
   75018602998,52028912648,35808955692,24456709450,16574674918,11145634448,7435995926,4921515890,
   3230905300,2103517016,1357963558,869101032,551330102,346604980,215907858,133245098,81458010,
   49326506,29584860,17574944,10340946,6026806,3479386,1989942,1127574,633086,352222,194198,
   106118,57458,30820,16372,8600,4460,2274,1136,552,254,108,40,10,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_18_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_18_p4 : List ℤ := pzig
  [0]
private def pvm_w0_18 : List ℤ :=
  pvm_w0_18_p0 ++ (pvm_w0_18_p1 ++ (pvm_w0_18_p2 ++ (pvm_w0_18_p3 ++ pvm_w0_18_p4)))
private def pvm_w0_19_p0 : List ℤ := pzig
  [5311708,29089824,110063292,331505642,840919608,1849601350,3585859526,6182318042,9509361824,
   13019363978,15715851268,16359877932,13946931654,8311198718,575600996,6938052477,11446905739,
   11017163747,5669375201,2169736442,8691099580,10455924054,6491894294,1043402789,7809545145,
   9771940751,5744788077,1801775502,8065174460,9006081760,4031954784,3553710085,8611602819,
   7710443589,1521379161,5630857860,8701749456,5553386986,1488392385,7339542791,7777436757,
   2543468183,4438830824,8023709862,5621908208,906971267,6622472645,7267712769,2465096885,
   4090216386,7428554154,5076945408,1060303809,6253518635,6593820319,1911279867,4128690636,
   6882084876,4329810024,1461932913,6019362853,5885678861,1256119475,4227044766,6367757010,
   3619506536,1830548671,5781711863,5252269051,748096711,4225666112,5910259650,3103316534,
   1995684443,5495308793,4799499369,530200971,4053497476,5542947932,2888095978,1863433245,
   5150018197,4587809757,678900253,3660234396,5267044056,3021540758,1373257367,4700156645,
   4603310995,1228840145,2967949584,5002600520,3475498994,466906859,4015866175,4722504937,
   2161569885,1850445368,4542438186,4100085246,888134064,2869188287,4654756625,3326975189,
   183571950,3531362866,4525436740,2567841154,1013132817,3897538173,4274120673,1948856845,
   1574357846,4073049420,4020841362,1508711140,1885357919,4105065857,3845172375,1301588929,
   1979481350,4060073516,3765144468,1320150356,1845019717,3937246977,3804856737]
private def pvm_w0_19_p1 : List ℤ := pzig
  [1564585219,1502962724,3711188728,3899279366,2014145600,911804057,3329443627,3993497639,
   2603272541,84282622,2694841554,3944062090,3248261736,978808470,1742426047,3609398195,
   3765373813,2176665789,401052126,2793560174,3934446250,3331726964,1270090338,1345287761,
   3406751757,4067391565,3062609023,795591105,1834117470,3797910640,4344881420,3270047188,
   956805722,1781914917,3990921813,4901225501,4189912433,2071328525,801811704,3561209268,
   5381829624,5713381618,4431388320,1859098958,1345992413,4385498077,6519705163,7230343193,
   6327685891,3980299731,654549909,3011076508,6345390234,8762338728,9850637858,9430696966,
   7563347292,4506489452,643531200,3586282681,7746674291,11457575727,14437771541,16521384479,
   17645123763,17822583195,17120234083,15632027821,13443850123,10591967485,7027845871,2590469469,
   3027488222,10330989986,20089535264,33415319038,51860855454,77553279658,113375830646,
   163195971798,232140924854,326932504204,456297062710,631456618634,866695944982,1179999644444,
   1593757966540,2135536212656,2838886722812,3744165880816,4899310993592,6360528962542,
   8192839535196,10470399005114,13276515723570,16703265917158,20850625041430,25825038072470,
   31737359834260,38700111230628,46824026792710,56213911861434,66963875521478,79152052146400,
   92834971436922,108041787413944,124768628236530,142973371459058,162571174043896,
   183431089988076,205374092784104,228172786290526,251553033174400,275197651423452,
   298752227836800,321832980692026,344036482567880,364950937264514,384168597563170,
   401298818521968,415981171688042,427898008031396,436785858360068,442445100987322,
   444747403871588,443640556158084,439150435534430,431380006388990]
private def pvm_w0_19_p2 : List ℤ := pzig
  [420505401118000,406769292302508,390471904820096,371960133473364,351615316001948,
   329840259849370,307046133135812,283639807051828,260012180895538,236527936715642,
   213517064866842,191268383587924,170025154541228,149982780836798,131288471272102,
   114042669127508,98301978894122,84083281431818,71368707644730,60111141774352,50239945274588,
   41666627042032,34290230855958,28002261497618,22691022960818,18245292065942,14557296139782,
   11525002452338,9053758656746,7057346972610,5458530272000,4189176124592,3190046264490,
   2410335205502,1807034306084,1344187844616,992096776402,726514718018,527870015268,380537968618,
   272178724574,193149173728,135991489168,94996656428,65838364782,45270768030,30882663592,
   20900365182,14031754198,9344519696,6172303754,4043259380,2626332578,1691352362,1079722316,
   683138434,428301720,266051088,163715838,99786576,60237336,36011400,21319434,12498740,7256322,
   4171974,2375558,1339726,748388,414124,227012,123284,66320,35328,18628,9714,5000,2532,1256,604,
   274,118,46,12,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0]
private def pvm_w0_19_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_19_p4 : List ℤ := pzig
  [0]
private def pvm_w0_19 : List ℤ :=
  pvm_w0_19_p0 ++ (pvm_w0_19_p1 ++ (pvm_w0_19_p2 ++ (pvm_w0_19_p3 ++ pvm_w0_19_p4)))
private def pvm_w0_20_p0 : List ℤ := pzig
  [253744,1617976,7173026,25494228,76974842,203531000,480390342,1023795988,1986791768,3524704270,
   5734358386,8543626584,11635909476,14361245990,15871031734,15249216306,11996691722,6262021002,
   801480829,7309487443,11146091107,10824578335,6345164227,619588890,7128205448,10231529592,
   8435272204,2525563824,4553937719,9123962291,8742954331,3568372493,3529987278,8494409850,
   8453757256,3417618290,3603564327,8317254623,7833657091,2479122039,4363621968,8313180618,
   6841611654,962837066,5446079165,8156209063,5389076285,931653492,6498488216,7565248954,
   3460213028,2940641321,7184572397,6375722111,1168744397,4748616920,7229271498,4580652706,
   1233109575,6047482151,6490645385,2327188193,3409067058,6596180552,5010868592,109616665,
   5044796249,6278516683,2990084629,2377111740,5926614982,5159475868,718580998,4154230011,
   5963143347,3463635095,1466038334,5248960114,5218795624,1474225662,3257892525,5591520537,
   3908897919,511656714,4487561322,5233435920,2286443178,2222803067,5100511623,4360073969,
   595479439,3515968090,5129719048,3178854916,935241627,4344592547,4724139961,1880377589,
   2190462802,4721809016,4039760126,653226364,3123078613,4761732133,3222574323,413136262,
   3727663120,4567915390,2426088764,1260290631,4083223241,4252875217,1719005859,1867461370,
   4238929482,3930708408,1176943598,2270345039,4276223383,3650196771,824455685,2466350194,
   4248509206,3484233476,670577630,2499184053,4176694973,3430801507]
private def pvm_w0_20_p1 : List ℤ := pzig
  [733730235,2352904804,4080837598,3504257208,991230848,2031795127,3910711315,3659979575,
   1453624787,1502594910,3633567806,3840148906,2060606490,747354321,3143326587,3938002329,
   2765115597,238308117,2378089524,3814995878,3414261482,1405751764,1245407705,3305920693,
   3839175967,2624229873,235146833,2250869436,3751270306,3636175910,1967675662,546585601,
   2858455523,4021156785,3573608397,1700447667,872715014,3171276140,4332345640,3916430076,
   2060689226,587741327,3121402501,4688975795,4763225427,3293684081,713237823,2205443410,
   4598369284,5770002644,5375915442,3492514116,580301040,2642885253,5391543955,7011072499,
   7122042183,5678894441,2952968913,538889322,4147149362,7225007236,9250132220,9899543514,
   9072845826,6880276776,3606696782,348134901,4544993189,8573706539,12096346603,14867087989,
   16740616759,17671017339,17693752731,16891281371,15355748783,13159598103,10329945921,
   6816094771,2448483139,3104450436,10381430288,20187933840,33684103922,52505067954,78912376416,
   115982695706,167849720938,240014140364,339726696894,476444417394,662364933570,913048480202,
   1248130902526,1692116606994,2275229206728,3034293758470,4013619979266,5265842190130,
   6852651570432,8845339957692,11325067265754,14382762010754,18118560060994,22640682365282,
   28063657005680,34505810682342,42085987140548,50919488380896,61113276308624,72760521305690,
   85934642996866,100683053233600,117020872333482,134924938315572,154328462158952,
   175116699919766,197124012522242,220132660077326,243873623879856,268029665391258,
   292240723366146,316111626236410,339221964112422,361137829080562,381425001043000,
   399663039666048]
private def pvm_w0_20_p2 : List ℤ := pzig
  [415459653417674,428464664477648,438382878851376,444985204801904,448117437469510,
   447706239813540,443761994716440,436378372032442,425728635608410,412058894613808,
   395678667062658,376949260049422,356270573219794,334066994482558,310773077281744,
   286819666523428,262621078132040,238563841324398,214997392184828,192226972769694,
   170508852458684,150047856979622,130997073047358,113459498707724,97491335456434,83106570455678,
   70282476118912,58965658235696,49078308991268,40524362732550,33195304688100,26975440839584,
   21746496212704,17391465272964,13797688955926,10859175992504,8478220248502,6566390239346,
   5044982056750,3845033593962,2906997600690,2180165392192,1621923628214,1196914948542,
   876160636238,636190843694,458215985560,327362188720,231984519290,163064239656,113690596700,
   78623497862,53930697560,36691547684,24758703084,16569171576,10996546184,7236982784,4722358450,
   3054968398,1959024758,1245065630,784141162,489300836,302461062,185187476,112291296,67425688,
   40087800,23598258,13753494,7936096,4533844,2564504,1436278,796524,437424,237888,128112,68310,
   36058,18836,9724,4952,2480,1214,576,262,110,38,10,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_20_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_20_p4 : List ℤ := pzig
  [0]
private def pvm_w0_20 : List ℤ :=
  pvm_w0_20_p0 ++ (pvm_w0_20_p1 ++ (pvm_w0_20_p2 ++ (pvm_w0_20_p3 ++ pvm_w0_20_p4)))
private theorem dk_w0_0 : muxFastIterBSlideChk 6 513 phbv_w0
    rkmViHi_m512_r512_s1_c0 pvm_w0_1 = true := by
  decide +kernel
private theorem dk_w0_1 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_1 pvm_w0_2 = true := by
  decide +kernel
private theorem dk_w0_2 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_2 pvm_w0_3 = true := by
  decide +kernel
private theorem dk_w0_3 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_3 pvm_w0_4 = true := by
  decide +kernel
private theorem dk_w0_4 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_4 pvm_w0_5 = true := by
  decide +kernel
private theorem dk_w0_5 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_5 pvm_w0_6 = true := by
  decide +kernel
private theorem dk_w0_6 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_6 pvm_w0_7 = true := by
  decide +kernel
private theorem dk_w0_7 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_7 pvm_w0_8 = true := by
  decide +kernel
private theorem dk_w0_8 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_8 pvm_w0_9 = true := by
  decide +kernel
private theorem dk_w0_9 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_9 pvm_w0_10 = true := by
  decide +kernel
private theorem dk_w0_10 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_10 pvm_w0_11 = true := by
  decide +kernel
private theorem dk_w0_11 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_11 pvm_w0_12 = true := by
  decide +kernel
private theorem dk_w0_12 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_12 pvm_w0_13 = true := by
  decide +kernel
private theorem dk_w0_13 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_13 pvm_w0_14 = true := by
  decide +kernel
private theorem dk_w0_14 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_14 pvm_w0_15 = true := by
  decide +kernel
private theorem dk_w0_15 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_15 pvm_w0_16 = true := by
  decide +kernel
private theorem dk_w0_16 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_16 pvm_w0_17 = true := by
  decide +kernel
private theorem dk_w0_17 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_17 pvm_w0_18 = true := by
  decide +kernel
private theorem dk_w0_18 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_18 pvm_w0_19 = true := by
  decide +kernel
private theorem dk_w0_19 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_19 pvm_w0_20 = true := by
  decide +kernel
private theorem dk_w0_20 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_20 rkmVoHi_m512_r512_s1_c0 = true := by
  decide +kernel
private theorem ptail_ok : rkmAllTrueF [
    muxIntListEq rkmHbHi_m512_r512_s1_c0 phbv_w0
  ] = true := by
  decide +kernel
private theorem pw_w0_1 : muxFastIterFullT16 12 513
    phbv_w0 rkmViHi_m512_r512_s1_c0 = pvm_w0_2 :=
  (muxFastIterFullT16_add 6 6 513 phbv_w0 rkmViHi_m512_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) (muxFastIterBSlideChk_sound dk_w0_0)).trans
      (muxFastIterBSlideChk_sound dk_w0_1))
private theorem pw_w0_2 : muxFastIterFullT16 18 513
    phbv_w0 rkmViHi_m512_r512_s1_c0 = pvm_w0_3 :=
  (muxFastIterFullT16_add 12 6 513 phbv_w0 rkmViHi_m512_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) pw_w0_1).trans
      (muxFastIterBSlideChk_sound dk_w0_2))
private theorem pw_w0_3 : muxFastIterFullT16 24 513
    phbv_w0 rkmViHi_m512_r512_s1_c0 = pvm_w0_4 :=
  (muxFastIterFullT16_add 18 6 513 phbv_w0 rkmViHi_m512_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) pw_w0_2).trans
      (muxFastIterBSlideChk_sound dk_w0_3))
private theorem pw_w0_4 : muxFastIterFullT16 30 513
    phbv_w0 rkmViHi_m512_r512_s1_c0 = pvm_w0_5 :=
  (muxFastIterFullT16_add 24 6 513 phbv_w0 rkmViHi_m512_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) pw_w0_3).trans
      (muxFastIterBSlideChk_sound dk_w0_4))
private theorem pw_w0_5 : muxFastIterFullT16 36 513
    phbv_w0 rkmViHi_m512_r512_s1_c0 = pvm_w0_6 :=
  (muxFastIterFullT16_add 30 6 513 phbv_w0 rkmViHi_m512_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) pw_w0_4).trans
      (muxFastIterBSlideChk_sound dk_w0_5))
private theorem pw_w0_6 : muxFastIterFullT16 42 513
    phbv_w0 rkmViHi_m512_r512_s1_c0 = pvm_w0_7 :=
  (muxFastIterFullT16_add 36 6 513 phbv_w0 rkmViHi_m512_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) pw_w0_5).trans
      (muxFastIterBSlideChk_sound dk_w0_6))
private theorem pw_w0_7 : muxFastIterFullT16 48 513
    phbv_w0 rkmViHi_m512_r512_s1_c0 = pvm_w0_8 :=
  (muxFastIterFullT16_add 42 6 513 phbv_w0 rkmViHi_m512_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) pw_w0_6).trans
      (muxFastIterBSlideChk_sound dk_w0_7))
private theorem pw_w0_8 : muxFastIterFullT16 54 513
    phbv_w0 rkmViHi_m512_r512_s1_c0 = pvm_w0_9 :=
  (muxFastIterFullT16_add 48 6 513 phbv_w0 rkmViHi_m512_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) pw_w0_7).trans
      (muxFastIterBSlideChk_sound dk_w0_8))
private theorem pw_w0_9 : muxFastIterFullT16 60 513
    phbv_w0 rkmViHi_m512_r512_s1_c0 = pvm_w0_10 :=
  (muxFastIterFullT16_add 54 6 513 phbv_w0 rkmViHi_m512_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) pw_w0_8).trans
      (muxFastIterBSlideChk_sound dk_w0_9))
private theorem pw_w0_10 : muxFastIterFullT16 66 513
    phbv_w0 rkmViHi_m512_r512_s1_c0 = pvm_w0_11 :=
  (muxFastIterFullT16_add 60 6 513 phbv_w0 rkmViHi_m512_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) pw_w0_9).trans
      (muxFastIterBSlideChk_sound dk_w0_10))
private theorem pw_w0_11 : muxFastIterFullT16 72 513
    phbv_w0 rkmViHi_m512_r512_s1_c0 = pvm_w0_12 :=
  (muxFastIterFullT16_add 66 6 513 phbv_w0 rkmViHi_m512_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) pw_w0_10).trans
      (muxFastIterBSlideChk_sound dk_w0_11))
private theorem pw_w0_12 : muxFastIterFullT16 78 513
    phbv_w0 rkmViHi_m512_r512_s1_c0 = pvm_w0_13 :=
  (muxFastIterFullT16_add 72 6 513 phbv_w0 rkmViHi_m512_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) pw_w0_11).trans
      (muxFastIterBSlideChk_sound dk_w0_12))
private theorem pw_w0_13 : muxFastIterFullT16 84 513
    phbv_w0 rkmViHi_m512_r512_s1_c0 = pvm_w0_14 :=
  (muxFastIterFullT16_add 78 6 513 phbv_w0 rkmViHi_m512_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) pw_w0_12).trans
      (muxFastIterBSlideChk_sound dk_w0_13))
private theorem pw_w0_14 : muxFastIterFullT16 90 513
    phbv_w0 rkmViHi_m512_r512_s1_c0 = pvm_w0_15 :=
  (muxFastIterFullT16_add 84 6 513 phbv_w0 rkmViHi_m512_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) pw_w0_13).trans
      (muxFastIterBSlideChk_sound dk_w0_14))
private theorem pw_w0_15 : muxFastIterFullT16 96 513
    phbv_w0 rkmViHi_m512_r512_s1_c0 = pvm_w0_16 :=
  (muxFastIterFullT16_add 90 6 513 phbv_w0 rkmViHi_m512_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) pw_w0_14).trans
      (muxFastIterBSlideChk_sound dk_w0_15))
private theorem pw_w0_16 : muxFastIterFullT16 102 513
    phbv_w0 rkmViHi_m512_r512_s1_c0 = pvm_w0_17 :=
  (muxFastIterFullT16_add 96 6 513 phbv_w0 rkmViHi_m512_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) pw_w0_15).trans
      (muxFastIterBSlideChk_sound dk_w0_16))
private theorem pw_w0_17 : muxFastIterFullT16 108 513
    phbv_w0 rkmViHi_m512_r512_s1_c0 = pvm_w0_18 :=
  (muxFastIterFullT16_add 102 6 513 phbv_w0 rkmViHi_m512_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) pw_w0_16).trans
      (muxFastIterBSlideChk_sound dk_w0_17))
private theorem pw_w0_18 : muxFastIterFullT16 114 513
    phbv_w0 rkmViHi_m512_r512_s1_c0 = pvm_w0_19 :=
  (muxFastIterFullT16_add 108 6 513 phbv_w0 rkmViHi_m512_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) pw_w0_17).trans
      (muxFastIterBSlideChk_sound dk_w0_18))
private theorem pw_w0_19 : muxFastIterFullT16 120 513
    phbv_w0 rkmViHi_m512_r512_s1_c0 = pvm_w0_20 :=
  (muxFastIterFullT16_add 114 6 513 phbv_w0 rkmViHi_m512_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) pw_w0_18).trans
      (muxFastIterBSlideChk_sound dk_w0_19))
private theorem pw_w0_20 : muxFastIterFullT16 126 513
    phbv_w0 rkmViHi_m512_r512_s1_c0 = rkmVoHi_m512_r512_s1_c0 :=
  (muxFastIterFullT16_add 120 6 513 phbv_w0 rkmViHi_m512_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) pw_w0_19).trans
      (muxFastIterBSlideChk_sound dk_w0_20))
/-- Certified `T_16` walk chunk `m512_r512_s1_c0`. -/
theorem rkmWalkChkHi_m512_r512_s1_c0 : muxFastIterFullT16 126 513
    rkmHbHi_m512_r512_s1_c0 rkmViHi_m512_r512_s1_c0 = rkmVoHi_m512_r512_s1_c0 :=
  (congrArg (fun h ↦ muxFastIterFullT16 126 513 h rkmViHi_m512_r512_s1_c0)
    (muxIntListEq_eq_true.mp (rkmHd ptail_ok))).trans pw_w0_20
/-- Standalone table witness (`FindAllJohnsonRampKickMuxHi512T5`). -/
theorem laneWitness_FindAllJohnsonRampKickMuxHi512T5 :
    rkmWalkChkHi_m512_r512_s1_c0 = rkmWalkChkHi_m512_r512_s1_c0 :=
  rfl
private theorem laneRoot_Hi512T5 : rkmZigHi512T5 = rkmZigHi512T5 :=
  (And.intro (Eq.refl rkmHbHi_m512_r512_s0_c1) rfl).right

end
end QuantumComputation.Specs.DickeSol
