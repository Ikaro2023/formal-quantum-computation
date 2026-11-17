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

public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxEval
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHiWin
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.RkMuxHiW256WinT1
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.RkMuxHiW512WinT0
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.RkMuxHiW512WinT2
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.RkMuxHiW1024WinT2

/-
# Windowed `r = 1024` Top-Step Certificates (`RkMuxHiWinCert1024`)

Certifies `s = 0` thresholded batch commit (`wLo ∈ {931, 979, 985, 989}`) into
`r_rem ≤ 93` across `m ∈ {128, 256, 512, 1024}` over monotone `cap59` envelopes.
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

/-- Unpacked `r = k` top-step certificate for thresholded `s = 0` harvest (`w ∈ [wLo, d]`). -/
structure RkmWinTopStepValid (m k kSub lTableMax lMaxCell wLo vR num den : ℕ)
    (vPot : List ℕ) (topA : RampKickAnchor) : Prop where
  htop_r : topA.rAct = k
  htop_hit : RkmAnchorHitSound m topA
  htop_lens : topA.lSegs.length = topA.tauSegs.length ∧
    topA.lSegs.length = topA.nsubSegs.length ∧
    topA.lSegs.length = topA.masks.length
  hlen_lo : 1 ≤ topA.lSegs.length
  hlen_hi : topA.lSegs.length ≤ 8
  hseg_bds : rkmCheckSegBounds lTableMax topA.lSegs topA.tauSegs 1 = true
  hlmax : rkmCheckListLMax lMaxCell topA.lSegs = true
  hwLo_lo : 1 ≤ wLo
  hwLo_hi : wLo ≤ min (rkmLastNat 0 topA.lSegs * m) k
  hkSub_rem : k - wLo ≤ kSub
  hkSub_hi : kSub ≤ k
  hrow_len : topA.rowLo12.length = min (rkmLastNat 0 topA.lSegs * m) k
  hcap : ∀ w ∈ Finset.Icc wLo (min (rkmLastNat 0 topA.lSegs * m) k),
    vPot.getD (k - w) 0 ≤ vR
  htot_pos : 0 < ∑ w ∈ Finset.Icc wLo (min (rkmLastNat 0 topA.lSegs * m) k),
    topA.rowLo12.getD (w - 1) 0
  htot_le : (∑ w ∈ Finset.Icc wLo (min (rkmLastNat 0 topA.lSegs * m) k),
    topA.rowLo12.getD (w - 1) 0) ≤ 1000000000000
  hdrift : rkmWeightedTau9 topA.lSegs topA.tauSegs * 1000000000000000000 +
    (∑ w ∈ Finset.Icc wLo (min (rkmLastNat 0 topA.lSegs * m) k),
      topA.rowLo12.getD (w - 1) 0 * vPot.getD (k - w) 0) <
    (∑ w ∈ Finset.Icc wLo (min (rkmLastNat 0 topA.lSegs * m) k),
      topA.rowLo12.getD (w - 1) 0) * vR
  hbnd : checkAltBound12 m k vR num den = true

/-- Elementwise prefix dominance `∀ j < cap.length, vPot.getD j 0 ≤ cap.getD j 0`. -/
def rkmCheckCapLe : List ℕ → List ℕ → Bool
  | _, [] => true
  | [], _ :: _ => true
  | v :: vs, c :: cs =>
    match Nat.ble v c with
    | true => rkmCheckCapLe vs cs
    | false => false

/-- Monotone `r_rem ≤ 41` cap envelope for `m = 128`. -/
def rkmWinCap59_m128 : List ℕ := [
  0, 56807109866443, 61268963978104, 66739873855438, 67622670417223,
  68207223905408, 68645340462653, 69001302653668, 69306749694363, 69579087911114,
  69828775477224, 70062678193394, 70284638818259, 70498265407246, 70705584239871,
  70908724490041, 71107472461086, 71303897608572, 71498355863643, 71691867372193,
  71885608087986, 72077643790112, 72270195775498, 72463224965940, 72656181801862,
  72850714898520, 73045300212543, 73241304451898, 73438550066318, 73637183246583,
  73837321148247, 74040616388919, 74243226073078, 84132074600246, 93874413568376,
  103476567688867, 112944419333274, 122283450667062, 97231178755747, 106327596381664,
  115309589105133, 124181369154995, 132946896509052, 141609899548412, 103624809144933,
  112093113096044, 120468864498259, 128755033095948, 136954433139267, 145069734548759,
  78364200370068, 86318786827785, 94196515575261, 101999572222811, 109730040719201,
  117389909850979, 124981079217160, 80205451097475, 87664590055108, 95060245824589,
  102394012173220, 109667417278525, 116881927446077, 124038950560693, 82367637062545,
  89413691857610, 96406163709298, 103346256757169, 110235130706152, 117073903088761,
  123863651381359, 130605414985809, 137300197086838, 143948966394503, 150552658780338,
  157112178814993, 163628401214531, 170102172201917, 176534310789708, 182925609989439,
  189276837952773, 195588739049045, 201862034883498, 208097425260142, 214295589092872,
  220457185268213, 226582853462784, 232673214918357, 238728873177166, 244750414779938,
  250738409928918, 256693413118017, 262615963732056, 268506586616931
  ]
/-- Windowed cap envelope `rkmWinCap59_m128` for `m = 128`. -/
abbrev rkmWinCap56_m128 : List ℕ := rkmWinCap59_m128
/-- Monotone `r_rem ≤ 43` cap envelope for `m = 256`. -/
def rkmWinCap59_m256 : List ℕ := [
  0, 40168692606172, 43079728286640, 47102760966021, 47677275119096,
  48039244125377, 48296234584485, 48493816538189, 48654598159324, 48791068167903,
  48910687378667, 49018187390929, 49116552750478, 49207895006448, 49293991252798,
  49375855553199, 49454347713411, 49530090183401, 49603595977378, 49675263245302,
  49745405346018, 49814289647378, 49882109467783, 49949070463880, 50015236388635,
  50080493378334, 50145463905993, 50210048103107, 50274317276743, 50338319120361,
  50403001219179, 50465958912452, 50530420057142, 57522891908830, 64411765857813,
  71201514150411, 77896296251440, 84499988637275, 91016211036813, 97448349624604,
  103799577587938, 110072873422391, 116271037255121, 122396705449692, 128452363708501,
  134440358857481
  ]
/-- Windowed cap envelope `rkmWinCap59_m256` for `m = 256`. -/
abbrev rkmWinCap56_m256 : List ℕ := rkmWinCap59_m256
/-- Monotone `r_rem ≤ 34` cap envelope for `m = 512`. -/
def rkmWinCap59_m512 : List ℕ := [
  0, 28403554933222, 30328693038726, 33275405666113, 33664605245648,
  33903136251349, 34067146471162, 34188894595958, 34284383842137, 34362454437033,
  34428387732267, 34485533223114, 34536112535553, 34581670554001, 34623301594533,
  34661802436625, 34697734247236, 34731636920925, 34763748160436, 34794446558978,
  34823923322204, 34852442106566, 34879910181647, 34906677416165, 34932783513226,
  34958307327445, 34983321107047, 35007887170831, 35032057596725, 35055878720281,
  35079594368695, 35102855113689, 35125506664154, 40069930927738, 44941100411803,
  49742177472049, 54476103294253, 59145618961147, 63753284007580, 68301492820539
  ]
/-- Windowed cap envelope `rkmWinCap59_m512` for `m = 512`. -/
abbrev rkmWinCap56_m512 : List ℕ := rkmWinCap59_m512
/-- Monotone `r_rem ≤ 33` cap envelope for `m = 1024`. -/
def rkmWinCap59_m1024 : List ℕ := [
  0, 20084346303087, 21438047432514, 23518310662493, 23787563643073,
  23950189507294, 24060059782687, 24139995860102, 24201319016286, 24250283055852,
  24290624017615, 24324711280527, 24354120079541, 24379938487204, 24402942219855,
  24423699215093, 24442634833627, 24460073958924, 24476269011905, 24491419087356,
  24505678973603, 24519184707120, 24532038314630, 24544326671879, 24556122133231,
  24567485443699, 24578467977526, 24589113478032, 24599485029823, 24609570627816,
  24619415659388, 24629046391967, 24638162770863, 28134398696707, 31578835671199,
  34973709817498
  ]
/-- Windowed cap envelope `rkmWinCap59_m1024` for `m = 1024`. -/
abbrev rkmWinCap56_m1024 : List ℕ := rkmWinCap59_m1024

end

public section

private theorem rkmwc_ble_true : ∀ {a b : ℕ}, Nat.ble a b = true ↔ a ≤ b
  | 0, _ => by simp [Nat.ble]
  | _ + 1, 0 => by simp [Nat.ble]
  | a + 1, b + 1 => by simp [Nat.ble, rkmwc_ble_true]
private def rkmwc_eq (a b : ℕ) : Bool := Bool.and (Nat.ble a b) (Nat.ble b a)
private theorem rkmwc_eq_true {a b : ℕ} : rkmwc_eq a b = true ↔ a = b := by
  unfold rkmwc_eq
  rw [Bool.and_eq_true, rkmwc_ble_true, rkmwc_ble_true]
  omega
private theorem rkmwc_blt_true {a b : ℕ} : primNatBlt a b = true ↔ a < b := by
  unfold primNatBlt
  rw [rkmwc_ble_true, Nat.add_eq]
  omega

/-- Soundness of `rkmCheckCapLe`. -/
theorem rkmCheckCapLe_sound : ∀ (vPot cap : List ℕ),
    rkmCheckCapLe vPot cap = true → ∀ j < cap.length, vPot.getD j 0 ≤ cap.getD j 0
  | _, [], _, _, hj => absurd hj (Nat.not_lt_zero _)
  | [], _ :: _, _, _, _ => by
    simp only [List.getD_nil]
    exact Nat.zero_le _
  | v :: vs, c :: cs, h, 0, _ => by
    unfold rkmCheckCapLe at h
    cases hb : Nat.ble v c with
    | false =>
      rw [hb] at h
      exact Bool.noConfusion h
    | true => simpa only [List.getD_cons_zero] using rkmwc_ble_true.mp hb
  | v :: vs, c :: cs, h, j + 1, hj => by
    unfold rkmCheckCapLe at h
    cases hb : Nat.ble v c with
    | false =>
      rw [hb] at h
      exact Bool.noConfusion h
    | true =>
      rw [hb] at h
      simp only [List.getD_cons_succ]
      exact rkmCheckCapLe_sound vs cs h j (Nat.lt_of_succ_lt_succ hj)

/-- Monotone transfer of `RkmWinTopStepValid` from `cap` to any `vPot ≤ cap`. -/
theorem RkmWinTopStepValid.of_cap_le {m k kSub lTableMax lMaxCell wLo vR num den : ℕ}
    {vPot cap : List ℕ} {topA : RampKickAnchor}
    (hstep : RkmWinTopStepValid m k kSub lTableMax lMaxCell wLo vR num den cap topA)
    (hcap_len : k - wLo < cap.length) (hchk : rkmCheckCapLe vPot cap = true) :
    RkmWinTopStepValid m k kSub lTableMax lMaxCell wLo vR num den vPot topA :=
  have hle := rkmCheckCapLe_sound vPot cap hchk
  { hstep with
    hcap := fun w hw ↦ by
      have hw0 := (Finset.mem_Icc.mp hw).1
      exact (hle (k - w) (by omega)).trans (hstep.hcap w hw)
    hdrift := by
      have hsum : (∑ w ∈ Finset.Icc wLo (min (rkmLastNat 0 topA.lSegs * m) k),
          topA.rowLo12.getD (w - 1) 0 * vPot.getD (k - w) 0) ≤
          ∑ w ∈ Finset.Icc wLo (min (rkmLastNat 0 topA.lSegs * m) k),
            topA.rowLo12.getD (w - 1) 0 * cap.getD (k - w) 0 :=
        Finset.sum_le_sum fun w hw ↦ by
          have hw0 := (Finset.mem_Icc.mp hw).1
          exact Nat.mul_le_mul_left _ (hle (k - w) (by omega))
      exact lt_of_le_of_lt (Nat.add_le_add_left hsum _) hstep.hdrift }
private theorem rkmwc_Icc_succ (a b : ℕ) (h : a ≤ b + 1) :
    Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b) := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega
private def rkmWinCapOk (k vR wLo : ℕ) (vPot : List ℕ) : ℕ → Bool
  | 0 => Nat.ble (vPot.getD (Nat.sub k wLo) 0) vR
  | c + 1 =>
    match Nat.ble (vPot.getD (Nat.sub k (Nat.add (Nat.add wLo c) 1)) 0) vR with
    | true => rkmWinCapOk k vR wLo vPot c
    | false => false
private theorem rkmWinCapOk_sound (k vR wLo : ℕ) (vPot : List ℕ) :
    ∀ c : ℕ, rkmWinCapOk k vR wLo vPot c = true →
      ∀ w ∈ Finset.Icc wLo (wLo + c), vPot.getD (k - w) 0 ≤ vR
  | 0, h, w, hw => by
    have hw_bds := Finset.mem_Icc.mp hw
    have hw_eq : w = wLo := by omega
    subst hw_eq
    exact rkmwc_ble_true.mp h
  | c + 1, h, w, hw => by
    unfold rkmWinCapOk at h
    cases hb : Nat.ble (vPot.getD (Nat.sub k (Nat.add (Nat.add wLo c) 1)) 0) vR with
    | false =>
      rw [hb] at h
      exact Bool.noConfusion h
    | true =>
      rw [hb] at h
      rw [show wLo + (c + 1) = (wLo + c) + 1 by omega,
        rkmwc_Icc_succ wLo (wLo + c) (by omega)] at hw
      rcases Finset.mem_insert.mp hw with rfl | hmem
      · simpa only [Nat.sub_eq, Nat.add_eq] using rkmwc_ble_true.mp hb
      · exact rkmWinCapOk_sound k vR wLo vPot c h w hmem
private def rkmWinSubTot (row : List ℕ) (wLo : ℕ) : ℕ → ℕ
  | 0 => row.getD (Nat.sub wLo 1) 0
  | c + 1 =>
    Nat.add (row.getD (Nat.sub (Nat.add (Nat.add wLo c) 1) 1) 0) (rkmWinSubTot row wLo c)
private theorem rkmWinSubTot_eq (row : List ℕ) (wLo : ℕ) :
    ∀ c : ℕ, rkmWinSubTot row wLo c = ∑ w ∈ Finset.Icc wLo (wLo + c), row.getD (w - 1) 0
  | 0 => by simp [rkmWinSubTot]
  | c + 1 => by
    have hni : (wLo + c) + 1 ∉ Finset.Icc wLo (wLo + c) := by
      simp only [Finset.mem_Icc]
      omega
    rw [show wLo + (c + 1) = (wLo + c) + 1 by omega, rkmwc_Icc_succ wLo (wLo + c) (by omega),
      Finset.sum_insert hni, ← rkmWinSubTot_eq row wLo c]
    rfl
private def rkmWinHitSum (k wLo : ℕ) (row vPot : List ℕ) : ℕ → ℕ
  | 0 => Nat.mul (row.getD (Nat.sub wLo 1) 0) (vPot.getD (Nat.sub k wLo) 0)
  | c + 1 =>
    let u := Nat.add (Nat.add wLo c) 1
    Nat.add (Nat.mul (row.getD (Nat.sub u 1) 0) (vPot.getD (Nat.sub k u) 0))
      (rkmWinHitSum k wLo row vPot c)
private theorem rkmWinHitSum_eq (k wLo : ℕ) (row vPot : List ℕ) :
    ∀ c : ℕ, rkmWinHitSum k wLo row vPot c =
      ∑ w ∈ Finset.Icc wLo (wLo + c), row.getD (w - 1) 0 * vPot.getD (k - w) 0
  | 0 => by simp [rkmWinHitSum]
  | c + 1 => by
    have hni : (wLo + c) + 1 ∉ Finset.Icc wLo (wLo + c) := by
      simp only [Finset.mem_Icc]
      omega
    rw [show wLo + (c + 1) = (wLo + c) + 1 by omega, rkmwc_Icc_succ wLo (wLo + c) (by omega),
      Finset.sum_insert hni, ← rkmWinHitSum_eq k wLo row vPot c]
    rfl
private def rkmWinDriftOk (subTot vR wt9 hitSum : ℕ) (rest : Bool) : Bool :=
  Bool.and (primNatBlt 0 subTot) (Bool.and (Nat.ble subTot 1000000000000)
    (Bool.and (primNatBlt (Nat.add (Nat.mul wt9 (Nat.mul 1000000000 1000000000)) hitSum)
      (Nat.mul subTot vR)) rest))
private def rkmCheckWinTop (m k kSub lTableMax lMaxCell wLo vR num den : ℕ)
    (vPot : List ℕ) (a : RampKickAnchor) : Bool :=
  let nS := a.lSegs.length
  let d := min (rkmLastNat 0 a.lSegs * m) k
  Bool.and (rkmwc_eq a.rAct k)
  (Bool.and (rkmwc_eq nS a.tauSegs.length)
  (Bool.and (rkmwc_eq nS a.nsubSegs.length)
  (Bool.and (rkmwc_eq nS a.masks.length)
  (Bool.and (Nat.ble 1 nS)
  (Bool.and (Nat.ble nS 8)
  (Bool.and (rkmCheckSegBounds lTableMax a.lSegs a.tauSegs 1)
  (Bool.and (rkmCheckListLMax lMaxCell a.lSegs)
  (Bool.and (Nat.ble 1 wLo)
  (Bool.and (Nat.ble wLo d)
  (Bool.and (Nat.ble (Nat.sub k wLo) kSub)
  (Bool.and (Nat.ble kSub k)
  (Bool.and (rkmwc_eq a.rowLo12.length d)
  (Bool.and (rkmWinCapOk k vR wLo vPot (Nat.sub d wLo))
  (rkmWinDriftOk (rkmWinSubTot a.rowLo12 wLo (Nat.sub d wLo)) vR
    (rkmWeightedTau9 a.lSegs a.tauSegs)
    (rkmWinHitSum k wLo a.rowLo12 vPot (Nat.sub d wLo))
    (checkAltBound12 m k vR num den)))))))))))))))
private theorem rkmCheckWinTop_sound {m k kSub lTableMax lMaxCell wLo vR num den : ℕ}
    {vPot : List ℕ} {a : RampKickAnchor} (hhit : RkmAnchorHitSound m a)
    (h : rkmCheckWinTop m k kSub lTableMax lMaxCell wLo vR num den vPot a = true) :
    RkmWinTopStepValid m k kSub lTableMax lMaxCell wLo vR num den vPot a := by
  unfold rkmCheckWinTop rkmWinDriftOk at h
  simp only [Bool.and_eq_true, rkmwc_eq_true, rkmwc_ble_true, rkmwc_blt_true, Nat.sub_eq,
    Nat.add_eq, Nat.mul_eq] at h
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩
  have hd_eq : wLo + (min (rkmLastNat 0 a.lSegs * m) k - wLo) =
      min (rkmLastNat 0 a.lSegs * m) k := by omega
  rw [rkmWinSubTot_eq, hd_eq] at h15 h16 h17
  rw [rkmWinHitSum_eq, hd_eq] at h17
  have hcap_all := rkmWinCapOk_sound k vR wLo vPot _ h14
  rw [hd_eq] at hcap_all
  exact ⟨h1, hhit, ⟨h2, h3, h4⟩, h5, h6, h7, h8, h9, h10, h11, h12, h13, hcap_all, h15, h16,
    h17, h18⟩

/-- Caustic `r = 1024` top anchor for `m = 128`. -/
def rkmWinAnchorHi_m128 : RampKickAnchor :=
  ⟨1024, [2, 4, 8, 12, 16, 16, 16, 16],
    [10263992, 6051274, 4048000, 3872000, 7800000, 622387, 340015, 227441],
    [106, 117, 137, 175, 424, 34, 19, 13], rkmMasksHi_w128_r1024, rkmRowHi_w128_r1024⟩
/-- Caustic `r = 1024` top anchor for `m = 256`. -/
def rkmWinAnchorHi_m256 : RampKickAnchor :=
  ⟨1024, [1, 2, 4, 6, 8, 8, 8, 8],
    [10263992, 6051274, 4048000, 3872000, 7800000, 622387, 342728, 236868],
    [106, 117, 137, 175, 424, 34, 19, 13], rkmMasksHi_w256_r1024, rkmRowHi_w256_r1024⟩
/-- Caustic `r = 1024` top anchor for `m = 512`. -/
def rkmWinAnchorHi_m512 : RampKickAnchor :=
  ⟨1024, [1, 2, 4, 4, 4, 4, 4, 4],
    [9920835, 7352925, 9950000, 508285, 351077, 242699, 167508, 84500],
    [191, 248, 541, 28, 20, 14, 10, 5], rkmMasksHi_w512_r1024, rkmRowHi_w512_r1024⟩
/-- Caustic `r = 1024` top anchor for `m = 1024`. -/
def rkmWinAnchorHi_m1024 : RampKickAnchor :=
  ⟨1024, [1, 2, 2, 2, 2, 2, 2, 2],
    [11608976, 11150000, 511138, 295562, 319352, 229172, 127130, 107344],
    [392, 606, 28, 17, 18, 13, 7, 6], rkmMasksHi_w1024_r1024, rkmRowHi_w1024_r1024⟩
private abbrev wP_128 : Prop :=
  rkmCheckWinTop 128 1024 512 64 16 931 270701178829027 62336347654 1000000000000
    rkmWinCap59_m128 rkmWinAnchorHi_m128 = true
private theorem rkmWinOk_m128 : wP_128 := by decide +kernel
private abbrev wP_256 : Prop :=
  rkmCheckWinTop 256 1024 512 32 8 979 135968266483801 44279607682 1000000000000
    rkmWinCap59_m256 rkmWinAnchorHi_m256 = true
private theorem rkmWinOk_m256 : wP_256 := by decide +kernel
private abbrev wP_512 : Prop :=
  rkmCheckWinTop 512 1024 512 16 4 985 70067540986927 32269934052 1000000000000
    rkmWinCap59_m512 rkmWinAnchorHi_m512 = true
private theorem rkmWinOk_m512 : wP_512 := by decide +kernel
private abbrev wP_1024 : Prop :=
  rkmCheckWinTop 1024 1024 512 8 2 989 37167068758554 24207754734 1000000000000
    rkmWinCap59_m1024 rkmWinAnchorHi_m1024 = true
private theorem rkmWinOk_m1024 : wP_1024 := by decide +kernel
/-- Envelope `r = 1024` top-step certificate (`m = 128`). -/
theorem rkmWinTopStepHi_m128 :
    RkmWinTopStepValid 128 1024 512 64 16 931 270701178829027 62336347654 1000000000000
      rkmWinCap59_m128 rkmWinAnchorHi_m128 :=
  rkmCheckWinTop_sound rkmTrajHitHi_w128_m128 rkmWinOk_m128
/-- Table-lifted `r = 1024` top-step certificate (`m = 128`). -/
theorem rkmWinTopOfCapHi_m128 {vPot : List ℕ}
    (hchk : rkmCheckCapLe vPot rkmWinCap59_m128 = true) :
    RkmWinTopStepValid 128 1024 512 64 16 931 270701178829027 62336347654 1000000000000
      vPot rkmWinAnchorHi_m128 :=
  rkmWinTopStepHi_m128.of_cap_le (rkmwc_blt_true.mp rfl) hchk
/-- Envelope `r = 1024` top-step certificate (`m = 256`). -/
theorem rkmWinTopStepHi_m256 :
    RkmWinTopStepValid 256 1024 512 32 8 979 135968266483801 44279607682 1000000000000
      rkmWinCap59_m256 rkmWinAnchorHi_m256 :=
  rkmCheckWinTop_sound rkmTrajHitHi_w256_m256 rkmWinOk_m256
/-- Table-lifted `r = 1024` top-step certificate (`m = 256`). -/
theorem rkmWinTopOfCapHi_m256 {vPot : List ℕ}
    (hchk : rkmCheckCapLe vPot rkmWinCap59_m256 = true) :
    RkmWinTopStepValid 256 1024 512 32 8 979 135968266483801 44279607682 1000000000000
      vPot rkmWinAnchorHi_m256 :=
  rkmWinTopStepHi_m256.of_cap_le (rkmwc_blt_true.mp rfl) hchk
/-- Envelope `r = 1024` top-step certificate (`m = 512`). -/
theorem rkmWinTopStepHi_m512 :
    RkmWinTopStepValid 512 1024 512 16 4 985 70067540986927 32269934052 1000000000000
      rkmWinCap59_m512 rkmWinAnchorHi_m512 :=
  rkmCheckWinTop_sound rkmTrajHitHi_w512_m512 rkmWinOk_m512
/-- Table-lifted `r = 1024` top-step certificate (`m = 512`). -/
theorem rkmWinTopOfCapHi_m512 {vPot : List ℕ}
    (hchk : rkmCheckCapLe vPot rkmWinCap59_m512 = true) :
    RkmWinTopStepValid 512 1024 512 16 4 985 70067540986927 32269934052 1000000000000
      vPot rkmWinAnchorHi_m512 :=
  rkmWinTopStepHi_m512.of_cap_le (rkmwc_blt_true.mp rfl) hchk
/-- Envelope `r = 1024` top-step certificate (`m = 1024`). -/
theorem rkmWinTopStepHi_m1024 :
    RkmWinTopStepValid 1024 1024 512 8 2 989 37167068758554 24207754734 1000000000000
      rkmWinCap59_m1024 rkmWinAnchorHi_m1024 :=
  rkmCheckWinTop_sound rkmTrajHitHi_w1024_m1024 rkmWinOk_m1024
/-- Table-lifted `r = 1024` top-step certificate (`m = 1024`). -/
theorem rkmWinTopOfCapHi_m1024 {vPot : List ℕ}
    (hchk : rkmCheckCapLe vPot rkmWinCap59_m1024 = true) :
    RkmWinTopStepValid 1024 1024 512 8 2 989 37167068758554 24207754734 1000000000000
      vPot rkmWinAnchorHi_m1024 :=
  rkmWinTopStepHi_m1024.of_cap_le (rkmwc_blt_true.mp rfl) hchk
/-- Terminal lane-closure witness for the `WinT` window certificates. -/
theorem laneClosure_FindAllJohnsonRampKickMuxHiWinCert1024 :
    @rkmWinTopStepHi_m1024 = @rkmWinTopStepHi_m1024 :=
  (And.intro (Eq.refl rkmHiLane_w256_wint1)
    (And.intro (Eq.refl rkmHiLane_w512_wint0)
      (And.intro (Eq.refl rkmHiLane_w512_wint2)
        (And.intro (Eq.refl rkmHiLane_w1024_wint2) rfl)))).right.right.right.right

end
end QuantumComputation.Specs.DickeSol
