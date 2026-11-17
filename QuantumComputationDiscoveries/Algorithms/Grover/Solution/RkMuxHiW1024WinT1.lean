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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.RkMuxHiW1024WinT0

/-
# Caustic `r = 1024` Halo-16 Walk `w1024` Part `1` (`RkMuxHiW1024WinT1`)

Certifies part `1` of the `w1024` `r = 1024` halo-16 trajectory.
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

/-- Generator list for `w1024_s1a`. -/
def rkmHbWin_w1024_s1a : List ℤ := altBuildHbFrom 2048 1024 18399339933 0 1024
/-- Entry `rkmXsWin_w1024_s1a_in`. -/
def rkmXsWin_w1024_s1a_in : List ℤ := let p := rkmP; [p 216399085, p 352741628, p 540374354,
  p 813011731, p 1071670895, p 1480618635, p 1932020500, p 2600069659, p 3475436604, p 4556647861,
  p 6005808848, p 7776122386, p 10147381802, p 13146905180, p 16967862185, p 21852668691,
  p 27962018104, p 35774572575, p 45526341919, p 57765614344, p 73011379679, p 91901708494,
  p 115380423524, p 144279916681, p 179883260557, p 223439707541, p 276553873416, p 341133765598,
  p 419226310834, p 513486535772, p 626682523591, p 762229624397, p 923901830468, p 1115929340419,
  p 1343266816387, p 1611209456988, p 1925959630982, p 2294180597133, p 2723316671304,
  p 3221588924693, p 3797776532728, p 4461648598945, p 5223423910298, p 6094188902794,
  p 7085596242511, p 8209821540571, p 9479732243840, p 10908331785132, p 12509114325589,
  p 14295478202969, p 16280791279573, p 18478209491328, p 20900180603333, p 23558612236783,
  p 26464111590029, p 29626103532526, p 33052347492688, p 36748585542908, p 40718526727144,
  p 44963059553705, p 49480489894572, p 54265808845790, p 59310791188990, p 64603663645318,
  p 70128915196042, p 75867286754623, p 81795637613732, p 87886932581392, p 94110530168943,
  p 100432002619391, p 106813726591055, p 113214899912627, p 119591961914950, p 125899310734077,
  p 132089300391765, p 138113468023071, p 143922582313896, p 149467531918336, p 154700184158929,
  p 159573497065522, p 164043004325205, p 168066810409379, p 171606581578615, p 174628256448213,
  p 177102111507558, p 179003872508366, p 180314581029985, p 181021236970253, p 181116920592806,
  p 180600812446747, p 179478420121739, p 177761107482782, p 175466386298674, p 172617159665909,
  p 169241609481627, p 165372829756240, p 161047868942375, p 156307683681782, p 151196017093216,
  p 145759050947328, p 140044522887977, p 134101140392598, p 127977915862059, p 121723379707476,
  p 115385053655193, p 109009004654693, p 102638920833816, p 96316192232355, p 90079112194382,
  p 83962730823970, p 77998726106266, p 72214794554816, p 66635258232458, p 61280288104137,
  p 56166336993091, p 51306379700307, p 46709511449797, p 42381795967827, p 38325935916954,
  p 34541853506448, p 31026943076106, p 27776130476182, p 24782495558026, p 22037220262103,
  p 19530339772025, p 17250547267602, p 15185697030266, p 13323172781858, p 11649887373129,
  p 10152573039562, p 8818089628377, p 7633273180772, p 6585567174673, p 5662577302690,
  p 4852610366787, p 4144637519253, p 3527939496897, p 2992952412392, p 2530540541380,
  p 2132356021228, p 1790832446277, p 1498870010598, p 1250312894485, p 1039459360705,
  p 861345785981, p 711385688875, p 585530879931, p 480380763586, p 392840845853, p 320153504589,
  p 260132815688, p 210602188773, p 170025901391, p 136828617234, p 109634759747, p 87594625595,
  p 69637993409, p 55091610802, p 43294663782, p 33759163517, p 26133088230, p 19927156215,
  p 15011998448, p 11084823078, p 7987431392, p 5578297343, p 3656728932, p 2230037992,
  p 1262556212, p 500822910, p 138749130]
/-- Exit `rkmXsWin_w1024_s1a_out`. -/
def rkmXsWin_w1024_s1a_out : List ℤ := let p := rkmP; [p 158112145, p 394919913, p 736676175,
  p 1448702712, p 2907239538, p 5516856900, p 10095465770, p 17946168944, p 31096125028,
  p 52194504869, p 85435740049, p 137084993889, p 215683091586, p 332808203844, p 504356193395,
  p 751027914247, p 1099882891629, p 1584785698671, p 2247923829123, p 3140880041470,
  p 4324817004044, p 5870711877066, p 7859081969191, p 10379121364203, p 13526597958393,
  p 17400699982914, p 22100696383616, p 27720869281346, p 34345296014080, p 42040955437696,
  p 50851414313062, p 60790157229270, p 71834534384046, p 83920691141040, p 96939506329818,
  p 110735072661167, p 125105281228127, p 139805260719462, p 154552286303158, p 169034563374711,
  p 182921864950789, p 195877739548999, p 207572767439490, p 217698980827272, p 225982961431268,
  p 232197927746071, p 236174814261907, p 237809158395958, p 237065776189803, p 233979810962986,
  p 228654462464561, p 221255283725062, p 212002212895852, p 201158316698335, p 189018043562358,
  p 175894470791886, p 162106167481647, p 147965015683778, p 133765495691665, p 119774919018507,
  p 106227192273935, p 93317556343328, p 81200231249571, p 69988315462769, p 59755099667374,
  p 50537126698772, p 42338759451980, p 35136616825522, p 28885503721670, p 23523446289248,
  p 18976825817261, p 15165462771223, p 12005951843048, p 9415714103246, p 7315190168573,
  p 5630065483728, p 4292607864922, p 3242136933067, p 2425853419570, p 1797984220707,
  p 1320033952406, p 959868966382, p 691058579687, p 492495582427, p 347106873360, p 241846084966,
  p 166378847789, p 112853942740, p 75410919185, p 49442504959, p 31831038979, p 19975953950,
  p 12158370308, p 7098993003, p 3809350975, p 1857000787, p 683781379, p 147730305]

end

public section

private abbrev fN {α : Type} (x : ℕ) (k : ℕ → α) : α := HighDForce.withForcedNat x k
private abbrev fL {α β : Type} (xs : List α) (k : List α → β) : β := HighDForce.withForcedList xs k
private theorem n1a (x : ℕ) : Nat.add 1 x = x + 1 := by rw [Nat.add_eq]; exact Nat.add_comm 1 x
private theorem ndiv (x y : ℕ) : Nat.div x y = x / y := rfl
private def uConsNat (x : ℕ) (xs : List ℕ) : List ℕ := match Nat.add 1 x with
  | 0 => xs | v + 1 => match xs with | [] => [v] | h :: t => v :: h :: t
private theorem uConsNat_eq (x : ℕ) (xs : List ℕ) : uConsNat x xs = x :: xs := by
  unfold uConsNat; rw [n1a]; cases xs <;> rfl
private def uToNatHb : List ℤ → Option (List ℕ)
  | [] => some []
  | Int.ofNat n :: xs => match uToNatHb xs with | some ns => some (uConsNat n ns) | none => none
  | Int.negSucc _ :: _ => none
private def uOfNatHb : List ℕ → List ℤ | [] => [] | n :: ns => Int.ofNat n :: uOfNatHb ns
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
  | [] => [] | u :: us => bConsZ (rkmForcedSubNatNat u z) (bDec z us)
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
    unfold bEnc1 at h; simp only [Nat.sub_eq, Nat.add_eq] at h; revert h
    cases hz : z - (k + 1) with
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
    have hm : (m : ℤ) - (n : ℤ) = Int.negSucc k := by rw [Int.negSucc_eq]; omega
    dsimp only; rw [hm]; dsimp only [zTdiv]; rw [bNeg_eq]
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
    dsimp only [rkmForcedIntAdd]; rw [bOfNatF_eq, Nat.add_eq]; simp [Int.ofNat_eq_natCast]
  | Int.ofNat m, Int.negSucc n => by
    dsimp only [rkmForcedIntAdd]; rw [bSub_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
    omega
  | Int.negSucc m, Int.ofNat n => by
    dsimp only [rkmForcedIntAdd]; rw [bSub_eq, Nat.add_eq, Int.negSucc_eq, Int.ofNat_eq_natCast]
    omega
  | Int.negSucc m, Int.negSucc n => by
    dsimp only [rkmForcedIntAdd]; rw [bNegSuccF_eq, Nat.add_eq, Nat.add_eq, Int.negSucc_eq]; omega
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
  | [] => true | x :: xs => cond (Nat.ble x 0) false (bAllPos xs)
private theorem bAllPos_cons {x : ℕ} {xs : List ℕ} (h : bAllPos (x :: xs) = true) :
    0 < x ∧ bAllPos xs = true := by
  cases x with | zero => exact Bool.noConfusion h | succ k => exact ⟨Nat.succ_pos k, h⟩
private theorem bAllPos_uCons {x : ℕ} {xs : List ℕ} (h : bAllPos (uConsNat x xs) = true) :
    0 < x ∧ bAllPos xs = true := by rw [uConsNat_eq] at h; exact bAllPos_cons h
private def bHeadOr (z : ℕ) : List ℕ → ℕ | [] => z | x :: _ => x
private def bTailN : List ℕ → List ℕ | [] => [] | _ :: xs => xs
private theorem bHeadOr_eq (z : ℕ) : ∀ (cs : List ℕ),
    ((bHeadOr z cs : ℤ) - (z : ℤ)) = (match bDec z cs with | cn :: _ => cn | [] => Int.ofNat 0)
  | [] => by unfold bHeadOr; rw [bDec_nil, bZero_eq]
  | c :: cs => by unfold bHeadOr; rw [bDec_cons]
private theorem bTailN_eq (z : ℕ) : ∀ (xs : List ℕ),
    bDec z (bTailN xs) = (match bDec z xs with | _ :: t => t | [] => [])
  | [] => rfl | x :: xs => by unfold bTailN; rw [bDec_cons]
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
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceList_eq] at h; revert h
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
    | none => none | some vNext => fN (rkmNextLen16 mL cL) fun nL => bIter z k mL nL bns vNext
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
      | none => muxUltraIterFullT16Rkm k mL cL hb v | some out => bDec z out
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
private def bWinStep (thr d : ℕ) (hb : List ℤ) (off : ℕ) (xs : List ℤ)
    (dropAcc : ℕ) : ℕ × List ℤ × ℕ :=
  fN (Nat.sub off 16) fun sLo => fN (Nat.sub off sLo) fun padL =>
    fN (Nat.sub (Nat.add d 1) sLo) fun remMax => fL (rkmDropInts sLo hb) fun hbSl =>
      fL (rkmPrependZeros padL xs) fun vecSl => fN (altIntLen vecSl) fun curLen =>
        fL (fIter 1 remMax curLen hbSl vecSl) fun rawSl => rkmTrimWin thr sLo rawSl dropAcc
private theorem bWinStep_eq (thr d : ℕ) (hb : List ℤ) (off : ℕ) (xs : List ℤ) (dropAcc : ℕ) :
    bWinStep thr d hb off xs dropAcc = muxWinStepT16 thr d hb off xs dropAcc := by
  unfold bWinStep muxWinStepT16; dsimp only [fN, fL]
  simp only [rkmb_forceNat_eq, rkmb_forceList_eq, fIter_eq]
private def bWinIter : ℕ → ℕ → ℕ → List ℤ → ℕ → List ℤ → ℕ → ℕ × List ℤ × ℕ
  | 0, _, _, _, off, xs, dropAcc => (off, xs, dropAcc)
  | k + 1, thr, d, hb, off, xs, dropAcc =>
    match bWinStep thr d hb off xs dropAcc with | (o1, x1, d1) => bWinIter k thr d hb o1 x1 d1
private theorem bWinIter_eq :
    ∀ (k thr d : ℕ) (hb : List ℤ) (off : ℕ) (xs : List ℤ) (dropAcc : ℕ),
      bWinIter k thr d hb off xs dropAcc = muxWinIterT16 k thr d hb off xs dropAcc
  | 0, _, _, _, _, _, _ => rfl
  | k + 1, thr, d, hb, off, xs, dropAcc => by
    unfold bWinIter muxWinIterT16; rw [bWinStep_eq]
    rcases muxWinStepT16 thr d hb off xs dropAcc with ⟨o1, x1, d1⟩
    exact bWinIter_eq k thr d hb o1 x1 d1
private def bNatEq (a b : ℕ) : Bool := Bool.and (Nat.ble a b) (Nat.ble b a)
private theorem bNatEq_eq_true {a b : ℕ} (h : bNatEq a b = true) : a = b := by
  unfold bNatEq at h; rw [Bool.and_eq_true, rkmw_nat_ble_eq_true, rkmw_nat_ble_eq_true] at h; omega
private def wSlChk (steps thr d : ℕ) (hb : List ℤ) (offIn : ℕ) (xsIn : List ℤ)
    (offOut : ℕ) (xsOut : List ℤ) (dropExp : ℕ) : Bool :=
  fL hb fun hbF => fL xsIn fun inF => fL xsOut fun outF =>
    match bWinIter steps thr d hbF offIn inF 0 with
    | (oRes, xRes, dRes) =>
      Bool.and (bNatEq oRes offOut) (Bool.and (muxIntListEq xRes outF) (bNatEq dRes dropExp))
private theorem wSlChk_sound {steps thr d offIn offOut dropExp : ℕ} {hb xsIn xsOut : List ℤ}
    (h : wSlChk steps thr d hb offIn xsIn offOut xsOut dropExp = true) :
    RkmWinIterSound steps d hb offIn xsIn offOut xsOut dropExp := by
  unfold wSlChk at h; dsimp only [fL] at h
  rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq, bWinIter_eq] at h
  rcases hres : muxWinIterT16 steps thr d hb offIn xsIn 0 with ⟨oRes, xRes, dRes⟩
  rw [hres] at h; simp only [Bool.and_eq_true] at h; rcases h with ⟨ho, hx, hd⟩
  have ho' := bNatEq_eq_true ho; have hd' := bNatEq_eq_true hd; subst ho'; subst hd'
  have h2 : muxWinIterT16HiChk steps thr 0 d hb offIn xsIn oRes xsOut dRes = true := by
    unfold muxWinIterT16HiChk; dsimp only
    rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq, hres]
    simp only [Bool.and_eq_true, rkmw_nat_beq_eq_true]; exact ⟨trivial, hx, trivial⟩
  exact muxWinIterT16HiChk_sound h2
private theorem rkmSubstHb {k d o0 o2 dT : ℕ} {hbF hbW x0 x2 : List ℤ}
    (hhb : muxIntListEq hbF hbW = true) (h : RkmWinIterSound k d hbF o0 x0 o2 x2 dT) :
    RkmWinIterSound k d hbW o0 x0 o2 x2 dT := by rw [← muxIntListEq_eq_true.mp hhb]; exact h
private theorem rkmChS (kT dT : ℕ) {k1 k2 d o0 o1 o2 d1 d2 : ℕ} {hb x0 x1 x2 : List ℤ}
    (h1 : RkmWinIterSound k1 d hb o0 x0 o1 x1 d1)
    (h2 : wSlChk k2 100000000 d hb o1 x1 o2 x2 d2 = true) (hk : k1 + k2 = kT) (hd : d1 + d2 = dT) :
    RkmWinIterSound kT d hb o0 x0 o2 x2 dT :=
  rkmChainWinIterT16 hk hd (muxIntListEq_eq_true.mpr rfl) rfl
    (muxIntListEq_eq_true.mpr rfl) h1 (wSlChk_sound h2)
private def pzig : List ℕ → List ℤ
  | [] => [] | w :: ws =>
    (match Nat.mod w 2 with
     | 0 => primOfNatForced (Nat.div w 2) | _ => primNegSuccForced (Nat.div w 2)) :: pzig ws
private def pzigCat : List (List ℕ) → List ℤ | [] => [] | ws :: wss => pzig ws ++ pzigCat wss
private theorem rkmWP0 {a : Bool} {s : List Bool} (h : rkmAllTrueF (a :: s) = true) : a = true :=
  (rkmAllTrueF_cons h).1
private def rkmHbF_w1024_s1a : List ℤ := pzigCat
  [
   [106580361510754,150616992196218,184332165220416,212692294992140,237622613570752,
    260111249329568,280745634856952,299908798420380,317866988162322,334814199774966,
    350896991283880,366229306618406,380901825242066,394988123025396,408548880919760,
    421634848276508,434288983709756,446548036466082,458443737312182,470003710728144,
    481252184227286,492210547384060,502897797763522,513330900531824,523525081339742,
    533494067022060,543250285051106,552805030071470,562168603925726,571350434155764,
    580359174892830,589202793235186,597888643587574,606423531952912,614813771788936,
    623065232745092,631183383359188,639173328604950,647039843030290,654787400103554,
    662420198285416,669942184262526,677357073711986,684668369910262,691879380454142,
    698993232322880,706012885478548,712941145174486,719780673118904,726533997621282,
    733203522832716,739791537177312,746300221059582,752731653922542,759087820722182,
    765370617876312,771581858739072,777723278646592,783796539574194,789803234441148,
    795744891095060,801622976004604,807438897686318,813194009888518,818889614553100,
    824526964573866,830107266368270,835631682277770,841101332810590,846517298739340,
    851880623064874,857192312856648,862453340978958,867664647711628,872827142272906,
    877941704251724,883009184955842,888030408681812,893006173912292,897937254445688,
    902824400462784,907668339534588,912469777575320,917229399744170,921947871299128,
    926625838405994,931263928905406,935862753040522,940422904147810,944944959313186,
    949429479995652,953877012620324,958288089142722,962663227585972,967002932552534,
    971307695711878,975577996265506,979814301390594,984017066663426,988186736463770,
    992323744361204,996428513484378,1000501456874148,1004542977821394,1008553470190386,
    1012533318728376,1016482899362208,1020402579482526,1024292718216286,1028153666688094,
    1031985768270968,1035789358827012,1039564766938530,1043312314130006,1047032315081416,
    1050725077833262,1054390903983728,1058030088878342,1061642921792446,1065229686106862,
    1068790659477012,1072326113995822,1075836316350664,1079321527974636,1082782005192370,
    1086217999360680,1089629757004210,1093017519946340],
   [1096381525435526,1099722006267278,1103039190901966,1106333303578614,1109604564424856,
    1112853189563210,1116079391213812,1119283377793786,1122465354013320,1125625520968660,
    1128764076232076,1131881213938962,1134977124872146,1138051996543568,1141106013273368,
    1144139356266528,1147152203687144,1150144730730406,1153117109692400,1156069510037790,
    1159002098465454,1161915038972176,1164808492914438,1167682619068396,1170537573688098,
    1173373510562000,1176190581067876,1178988934226114,1181768716751524,1184530073103660,
    1187273145535730,1189998074142144,1192704996904728,1195394049737664,1198065366531212,
    1200719079194208,1203355317695446,1205974210103914,1208575882627964,1211160459653448,
    1213728063780826,1216278815861312,1218812835032066,1221330238750482,1223831142827572,
    1226315661460508,1228783907264328,1231235991302830,1233672023118694,1236092110762846,
    1238496360823082,1240884878451990,1243257767394178,1245615130012828,1247957067315618,
    1250283678979998,1252595063377860,1254891317599616,1257172537477704,1259438817609538,
    1261690251379896,1263926930982810,1266148947442920,1268356390636348,1270549349311078,
    1272727911106870,1274892162574722,1277042189195886,1279178075400448,1281299904585492,
    1283407759132868,1285501720426538,1287581868869566,1289648283900706,1291701044010650,
    1293740226757892,1295765908784280,1297778165830198,1299777072749446,1301762703523784,
    1303735131277178,1305694428289736,1307640666011346,1309573915075034,1311494245310042,
    1313401725754632,1315296424668614,1317178409545634,1319047747125198,1320904503404446,
    1322748743649696,1324580532407750,1326399933516972,1328207010118138,1330001824665074,
    1331784438935090,1333554914039188,1335313310432088,1337059687922038,1338794105680454,
    1340516622251354,1342227295560614,1343926182925052,1345613341061326,1347288826094674,
    1348952693567476,1350604998447658,1352245795136946,1353875137478944,1355493078767082,
    1357099671752402,1358694968651206,1360279021152562,1361851880425660,1363413597127054,
    1364964221407758,1366503802920208,1368032390825114,1369550033798170,1371056780036662,
    1372552677265938,1374037772745780,1375512113276648,1376975745205830,1378428714433462,
    1379871066418462,1381302846184354,1382724098324982],
   [1384134867010134,1385535195991066,1386925128605936,1388304707785130,1389673976056516,
    1391032975550588,1392381748005546,1393720334772268,1395048776819212,1396367114737232,
    1397675388744308,1398973638690210,1400261904061068,1401540223983880,1402808637230938,
    1404067182224190,1405315897039512,1406554819410936,1407783986734786,1409003436073764,
    1410213204160956,1411413327403786,1412603841887900,1413784783380984,1414956187336536,
    1416118088897558,1417270522900204,1418413523877368,1419547126062212,1420671363391642,
    1421786269509726,1422891877771062,1423988221244098,1425075332714386,1426153244687804,
    1427221989393718,1428281598788094,1429332104556574,1430373538117484,1431405930624826,
    1432429312971196,1433443715790678,1434449169461684,1435445704109752,1436433349610310,
    1437412135591392,1438382091436314,1439343246286312,1440295629043140,1441239268371630,
    1442174192702224,1443100430233448,1444018008934362,1444926956546988,1445827300588676,
    1446719068354450,1447602286919326,1448476983140588,1449343183660024,1450200914906152,
    1451050203096394,1451891074239228,1452723554136310,1453547668384558,1454363442378220,
    1455170901310906,1455970070177580,1456760973776548,1457543636711400,1458318083392926,
    1459084338041022,1459842424686542,1460592367173154,1461334189159146,1462067914119222,
    1462793565346268,1463511165953096,1464220738874160,1464922306867256,1465615892515186,
    1466301518227418,1466979206241706,1467648978625700,1468310857278528,1468964863932354,
    1469611020153932,1470249347346114,1470879866749356,1471502599443202,1472117566347742,
    1472724788225050,1473324285680612,1473916079164732,1474500188973910,1475076635252214,
    1475645437992628,1476206617038384,1476760192084276,1477306182677954,1477844608221214,
    1478375487971246,1478898841041896,1479414686404886,1479923042891034,1480423929191456,
    1480917363858744,1481403365308132,1481881951818666,1482353141534318,1482816952465134,
    1483273402488328,1483722509349382,1484164290663132,1484598763914830,1485025946461200,
    1485445855531482,1485858508228452,1486263921529448,1486662112287360,1487053097231628,
    1487436892969216,1487813515985570,1488182982645580,1488545309194518,1488900511758960,
    1489248606347708,1489589608852696,1489923535049880],
   [1490250400600124,1490570221050068,1490883011832992,1491188788269668,1491487565569192,
    1491779358829818,1492064183039778,1492342053078080,1492612983715324,1492876989614474,
    1493134085331642,1493384285316858,1493627603914834,1493864055365698,1494093653805750,
    1494316413268188,1494532347683826,1494741470881816,1494943796590338,1495139338437314,
    1495328109951076,1495510124561058,1495685395598460,1495853936296906,1496015759793108,
    1496170879127496,1496319307244870,1496461056995018,1496596141133342,1496724572321468,
    1496846363127856,1496961526028396,1497070073406998,1497172017556176,1497267370677620,
    1497356144882774,1497438352193382,1497514004542062,1497583113772834,1497645691641672,
    1497701749817034,1497751299880390,1497794353326740,1497830921565130,1497861015919152,
    1497884647627454,1497901827844228,1497912567639698,1497916878000604,1497914769830670,
    1497906253951084,1497891341100948,1497870041937744,1497842367037784,1497808326896648,
    1497767931929632,1497721192472172,1497668118780280,1497608721030960,1497543009322626,
    1497470993675514,1497392684032084,1497308090257420,1497217222139628,1497120089390222,
    1497016701644502,1496907068461948,1496791199326572,1496669103647304,1496540790758342,
    1496406269919520,1496265550316652,1496118641061882,1495965551194032,1495806289678932,
    1495640865409756,1495469287207356,1495291563820570,1495107703926558,1494917716131106,
    1494721608968938,1494519390904016,1494311070329846,1494096655569774,1493876154877270,
    1493649576436220,1493416928361206,1493178218697780,1492933455422748,1492682646444428,
    1492425799602914,1492162922670348,1491894023351162,1491619109282336,1491338188033648,
    1491051267107910,1490758353941216,1490459455903170,1490154580297114,1489843734360368,
    1489526925264440,1489204160115250,1488875445953342,1488540789754096,1488200198427940,
    1487853678820542,1487501237713018,1487142881822122,1486778617800440,1486408452236574,
    1486032391655332,1485650442517896,1485262611222010,1484868904102144,1484469327429666,
    1484063887413004,1483652590197810,1483235441867116,1482812448441480,1482383615879148,
    1481948950076194,1481508456866660,1481062142022698,1480610011254702,1480152070211442,
    1479688324480192,1479218779586856,1478743440996078],
   [1478262314111374,1477775404275236,1477282716769240,1476784256814164,1476280029570078,
    1475770040136450,1475254293552238,1474732794795986,1474205548785912,1473672560379990,
    1473133834376036,1472589375511780,1472039188464946,1471483277853326,1470921648234838,
    1470354304107598,1469781249909976,1469202490020658,1468618028758694,1468027870383558,
    1467432019095178,1466830479033998,1466223254281006,1465610348857774,1464991766726490,
    1464367511789988,1463737587891774,1463101998816048,1462460748287722,1461813839972440,
    1461161277476584,1460503064347282,1459839204072422,1459169700080642,1458494555741334,
    1457813774364640,1457127359201438,1456435313443332,1455737640222634,1455034342612348,
    1454325423626140,1453610886218320,1452890733283804,1452164967658082,1451433592117182,
    1450696609377626,1449954022096384,1449205832870834,1448452044238698,1447692658677994,
    1446927678606970,1446157106384050,1445380944307758,1444599194616650,1443811859489240,
    1443018941043924,1442220441338894,1441416362372054,1440606706080930,1439791474342576,
    1438970668973476,1438144291729450,1437312344305532,1436474828335884,1435631745393660,
    1434783096990906,1433928884578428,1433069109545680,1432203773220616,1431332876869574,
    1430456421697132,1429574408845966,1428686839396704,1427793714367784,1426895034715288,
    1425990801332794,1425081015051208,1424165676638602,1423244786800038,1422318346177396,
    1421386355349198,1420448814830414,1419505725072282,1418557086462112,1417602899323090,
    1416643163914074,1415677880429390,1414707048998612,1413730669686364,1412748742492078,
    1411761267349786,1410768244127880,1409769672628880,1408765552589192,1407755883678868,
    1406740665501350,1405719897593220,1404693579423938,1403661710395576,1402624289842550,
    1401581317031344,1400532791160226,1399478711358970,1398419076688556,1397353886140876,
    1396283138638434,1395206833034038,1394124968110482,1393037542580234,1391944555085104,
    1390846004195918,1389741888412184,1388632206161740,1387516955800418,1386396135611684,
    1385269743806272,1384137778521828,1383000237822534,1381857119698722,1380708422066498,
    1379554142767346,1378394279567728,1377228830158686,1376057792155420,1374881163096880,
    1373698940445330,1372511121585928,1371317703826280],
   [1370118684395990,1368914060446216,1367703829049202,1366487987197818,1365266531805072,
    1364039459703642,1362806767645370,1361568452300780,1360324510258560,1359074938025052,
    1357819732023726,1356558888594662,1355292403993996,1354020274393384,1352742495879440,
    1351459064453182,1350169976029444,1348875226436312,1347574811414522,1346268726616864,
    1344956967607576,1343639529861724,1342316408764576,1340987599610960,1339653097604632,
    1338312897857600,1336966995389478,1335615385126792,1334258061902306,1332895020454322,
    1331526255425970,1330151761364490,1328771532720510,1327385563847294,1325993849000004,
    1324596382334928,1323193157908712,1321784169677570,1320369411496490,1318948877118426,
    1317522560193468,1316090454268020,1314652552783944,1313208849077704,1311759336379498,
    1310304007812362,1308842856391284,1307375875022282,1305903056501484,1304424393514180,
    1302939878633878,1301449504321328,1299953262923542,1298451146672794,1296943147685604,
    1295429257961716,1293909469383050,1292383773712636,1290852162593546,1289314627547800,
    1287771159975250,1286221751152458,1284666392231556,1283105074239076,1281537788074776,
    1279964524510446,1278385274188682,1276800027621662,1275208775189892,1273611507140922,
    1272008213588072,1270398884509098,1268783509744880,1267162078998052,1265534581831640,
    1263901007667656,1262261345785686,1260615585321448,1258963715265328,1257305724460900,
    1255641601603408,1253971335238242,1252294913759374,1250612325407780,1248923558269832,
    1247228600275668,1245527439197524,1243820062648066,1242106458078662,1240386612777646,
    1238660513868558,1236928148308344,1235189502885522,1233444564218346,1231693318752900,
    1229935752761198,1228171852339234,1226401603404998,1224624991696468,1222842002769570,
    1221052621996090,1219256834561572,1217454625463166,1215645979507444,1213830881308182,
    1212009315284104,1210181265656586,1208346716447322,1206505651475954,1204658054357658,
    1202803908500690,1200943197103896,1199075903154162,1197202009423848,1195321498468148,
    1193434352622430,1191540553999514,1189640084486908,1187732925743994,1185819059199172,
    1183898466046948,1181971127244964,1180037023510992,1178096135319864,1176148442900346,
    1174193926231966,1172232565041778,1170264338801062],
   [1168289226721984,1166307207754180,1164318260581280,1162322363617372,1160319495003400,
    1158309632603506,1156292754001280,1154268836495972,1152237857098610,1150199792528058,
    1148154619206998,1146102313257836,1144042850498530,1141976206438344,1139902356273522,
    1137821274882864,1135732936823250,1133637316325044,1131534387287432,1129424123273662,
    1127306497506196,1125181482861762,1123049051866312,1120909176689890,1118761829141384,
    1116606980663184,1114444602325734,1112274664821980,1110097138461686,1107911993165668,
    1105719198459886,1103518723469430,1101310536912382,1099094607093544,1096870901898052,
    1094639388784852,1092400034780036,1090152806470046,1087897669994744,1085634591040314,
    1083363534832042,1081084466126930,1078797349206146,1076502147867334,1074198825416740,
    1071887344661182,1069567667899838,1067239756915860,1064903572967810,1062559076780900,
    1060206228538044,1057844987870712,1055475313849588,1053097164975000,1050710499167160,
    1048315273756174,1045911445471816,1043498970433088,1041077804137532,1038647901450296,
    1036209216592952,1033761703132052,1031305313967416,1028840001320158,1026365716720410,
    1023882410994776,1021390034253476,1018888535877184,1016377864503554,1013857968013424,
    1011328793516674,1008790287337748,1006242395000826,1003685061214612,1001118229856770,
    998541843957950,995955845685430,993360176326336,990754776270448,988139584992550,
    985514541034354,982879581985932,980234644466694,977579664105844,974914575522346,
    972239312304350,969553806988082,966857991036164,964151794815358,961435147573708,
    958707977417064,955970211284968,953221774925874,950462592871684,947692588411584,
    944911683565144,942119799054658,939316854276714,936502767272944,933677454699938,
    930840831798298,927992812360792,925133308699572,922262231612434,919379490348088,
    916484992570384,913578644321470,910660349983840,907730012241236,904787532038344,
    901832808539254,898865739084650,895886219147638,892894142288208,889889400106244,
    886871882193058,883841476081334,880798067193502,877741538788394,874671771906170,
    871588645311438,868492035434458,865381816310404,862257859516552,859120034107362,
    855968206547318,852802240641454,849621997463470],
   [846427335281334,843218109480248,839994172482876,836755373666722,833501559278506,
    830232572345436,826948252583206,823648436300600,820332956300528,817001641777340,
    813654318210236,810290807252608,806910926617088,803514489956148,800101306737988,
    796671182117512,793223916802156,789759306912292,786277143835956,782777214077622,
    779259299100682,775723175163380,772168613147772,768595378381438,765003230451512,
    761391923010616,757761203574320,754110813309604,750440486813872,746749951883986,
    743038929274762,739307132446332,735554267299744,731780031900124,727984116186680,
    724166201668752,720325961107138,716463058179726,712577147130576,708667872401356,
    704734868244090,700777758314024,696796155241358,692789660180468,688757862335194,
    684700338458586,680616652325422,676506354175672,672368980126924,668204051553616,
    664011074430790,659789538639820,655538917233396,651258665656836,646948220922466,
    642607000733594,638234402554260,633829802620606,629392554889318,624921989918182,
    620417413673326,615878106257176,611303320550614,606692280762144,602044180876164,
    597358182991638,592633415541564,587868971382608,583063905743150,578217234016698,
    573327929386200,568394920263122,563417087523368,558393261519938,553322218849944,
    548202678850808,543033299797376,537812674768204,532539327145086,527211705705296,
    521828179260564,516387030790564,510886451011392,505324531311098,499699255974454,
    494008493607518,488249987659034,482421345919608,476520028860606,470543336652168,
    464488394672722,458352137290100,452131289655410,445822347203742,439421552498510,
    432924868986218,426327951142404,419626110383122,412814275983918,405886950082510,
    398838155632286,391661375908066,384349483825358,376894658894828,369288289060886,
    361520853919178,353581784804706,345459295892636,337140178615276,328609549160436,
    319850535260014,310843883414562,301567460362084,291995611755592,282098324634384,
    271840114919928,261178520821316,250062016782128,238427049797864,226193699630078,
    213259090703444,199486943484268,184690077727194,168599006039870,150800110080826,
    130597099502922,106632288410320,75400486065764]]
private def rkmC_w1024_s1a_1 : List ℤ := pzigCat
  [
   [287905278,575616328,1021683392,1404472058,2011099434,2688960214,3617846994,4902790186,
    6428255062,8550398518,11095367548,14519029248,18857893828,24453987042,31641553530,
    40725955906,52249259418,66755991578,84917886430,107749959982,136190960448,171651685800,
    215616024988,269787596930,336527292754,418108463768,517799944578,638975450060,785691255738,
    962954055434,1175913428654,1431273319804,1735975635398,2098203177408,2527399561226,
    3033590439198,3628851678962,4325865012428,5139004156130,6084121399558,7178077778550,
    8439794771614,9889113408954,11547582109662,13437932230404,15584018458052,18010986317754,
    20744478314102,23811257056684,27237793175312,31050962200920,35276978031424,39941120342598,
    45067580752852,50678498237938,56793525313798,63429547772450,70599465553000,78312271772580,
    86571966499438,95377163894524,104720670652860,114588405707208,124960041118872,
    135807420050118,147095236313804,158780785035196,170813046234984,183134205224428,
    195678512270890,208373595929172,221140840592086,233895512962088,246548760420548,
    259007140983504,271174820480176,282954280541978,294247587607362,304957823677224,
    314990483598336,324254761848398,332664925666532,340141493262802,346613038126714,
    352016479800048,356298877547956,359418041994420,361342738158400,362054313591844,
    361545567786414,359822016280862,356901498258608,352813277457480,347598694274316,
    341309133126168,334006460070846,325761179199620,316651321907502,306761825708728,
    296182764521588,285007821124020,273333463412998,261256975214620,248875774347334,
    236285390087222,223578917069638,210845875636574,198170517045378,185632413733164,
    173304205484280,161251933728944,149534803155364,138203888786714,127303413172644,
    116869532122938,106931126875928,97509910434724,88620692278692,80271946820090,72466104702624,
    65199969109958,58465841094266,52251422372192,46541214977632,41316118125768,36554455826126,
    32233411565816,28327821654838],
   [24812147283682,21660034146530,18844915533940,16340970855048,14122147668856,12163784895018,
    10441882721564,8933705700372,7617761366086,6473632902266,5483030550102,4628308314278,
    3893685746472,3264720699876,2728121563330,2272252001868,1886068135096,1560380047850,
    1286648056716,1057387571634,866239083006,707191976754,575631204548,466983390928,377627696236,
    304414025788,244399537870,195599201208,155747589532,123461444824,97302522686,76073590212,
    59099803272,45306847906,34387222774,25613054474,18628484486,13216876296,8862277200,
    5685981630,3232520658,1568988898,569577212]]
private def rkmC_w1024_s1a_2 : List ℤ := pzigCat
  [
   [420021790,748706308,1146870038,1703083582,2352662976,3188289978,4276454524,5566325106,
    7370982834,9699219324,12676900258,16662369166,21568695712,27946784748,36012434752,
    46196469592,59182065192,75373787476,95895409518,121445548992,153352953844,193085534380,
    241928656378,302343871186,376275422032,466756997038,577093837444,710972220396,872942163550,
    1068066463792,1302250052330,1582374473550,1916003972726,2312049954006,2780263626010,
    3331690764430,3978835939548,4735232616708,5616160180452,6637904020428,7818595395372,
    9177630283938,10735614227494,12515285127648,14539647782404,16833585931760,19422649250708,
    22332982214264,25591506623124,29224996229316,33260093725180,37722895942536,42637982904544,
    48028816703356,53916355462862,60318852144948,67251462118128,74724839813402,82745644800044,
    91314888470990,100428033010228,110074489215150,120236535156352,130889942975944,
    142002249146790,153534090970622,165438163537250,177659139590808,190134780568760,
    202795501619640,215564795277776,228360529290582,241094930456304,253676180791322,
    266009047118500,277995973700880,289538854123560,300539435397678,310901766278350,
    320532537321700,329343104680574,337251114517246,344180601695650,350064859498224,
    354845989920982,358476609522158,360920918063648,362154184135146,362164496318314,
    360951858198946,358528881332216,354920230105822,350162210693432,344302623603356,
    337398896934534,329518592996274,320737228587732,311137414570982,300807745025358,
    289840718716780,278332710485108,266381200271142,254084107845932,241538373714544,
    228838678115090,216076911881320,203339765477058,190709264400370,178261251626692,
    166064861489308,154182417734412,142668331684766,131570081477118,120926896362496,
    110770704747196,101126255422118,92010877349970,83435735109010,75405144002662,67918287868014,
    60969049947440,54546632434072,48636714065362,43221084867610,38279409130596,33788695173748,
    29724456136842,26061255931628],
   [22772561839824,19832157821192,17213307179374,14890079911134,12837139258744,11029878372900,
    9445267045656,8060917543066,6856339639730,5812091237336,4910217772528,4134435014122,
    3469365479588,2901592254660,2418504315996,2009066956382,1663430072640,1372557177216,
    1128940199618,925425873104,756195239468,615942603108,500006594436,404678685320,326286866768,
    262219972812,209868628194,167209885840,132655710418,104534757818,81943269724,63642132454,
    48957433290,37223722700,27749360510,20349489596,14400157978,9855499910,6383912434,3771630490,
    2038060552,801904248,225687162]]
private def rkmC_w1024_s1a_3 : List ℤ := pzigCat
  [
   [520641712,962370718,1297646108,1906765236,2607146346,3417064352,4658484182,6112006614,
    8138969496,10736401174,14047530992,18396472938,23684332770,30679374302,39445293218,
    50664634808,64906239394,82761497386,105236888266,133216197090,168069729388,211393871534,
    264771124176,330598745424,411316014900,509852210490,630080802598,775708861988,951774801878,
    1163775419582,1417815048762,1721444568464,2082722205602,2511262906106,3017294428122,
    3612705489878,4310801310618,5125596107048,6073509413366,7171673936366,8439031734374,
    9896083891582,11564283735934,13467174420206,15628896239634,18074988643946,20831712809004,
    23925937736522,27385003187170,31235776129264,35505375083046,40219388341002,45402386675722,
    51077009005106,57262879333828,63977230921946,71232940546972,79038924412896,87398961268578,
    96311220167968,105768074122042,115754663230906,126249729878732,137224101753114,
    148641125960016,160456457275682,172617470036606,185064441459102,197729554596084,
    210538418701610,223410165538794,236258063630980,248990836293568,261512769159798,
    273726213346258,285531562870418,296828943797446,307519968960288,317508635697564,
    326703548541170,335017992770038,342372474204278,348695645692118,353925124794352,
    358009153101766,360906480557204,362588238774690,363037460038550,362249735958786,
    360233564668120,357009406396020,352610394196604,347080729561926,340475816389876,
    332860970982560,324309966255262,314904680282406,304732787506256,293887461692878,
    282465156460712,270564401168792,258284819823470,245724954929276,232982046073836,
    220149798164272,207317988270972,194571381422296,181988464136812,169641637573982,
    157595645767536,145908197137440,134629143400584,123800422089126,113456588445478,
    103624110911128,94322729592144,85564936374268,77356921422902,69699108322546,62586170216760,
    56008550781460,49952066141858,44399350074708,39330038543542,34721238514338,30548684689554,
    26786330442658,23407796270356],
   [20386048417004,17694117359926,15305642196676,13194514388916,11336038272486,9706188771360,
    8282421589286,7043545520520,5969515369958,5042165968180,4244304627206,3560586830328,
    2976857362848,2480332395106,2059677048026,1704592759314,1405956948464,1155938558726,
    947086808756,773588126562,629774947220,510890421992,413242187798,332909876208,267263669864,
    213703719418,170126863638,134809551560,106070975292,83062301166,64441018308,49457450244,
    37446891898,27795193398,20352495260,14432619630,9922388444,6445608282,3802868526,2039909420,
    793888574,220749022]]
private def rkmC_w1024_s1a_4 : List ℤ := pzigCat
  [
   [319250092,670537030,977266890,1380401040,2010361822,2676866292,3772706266,5027561982,
    6713507030,8883991008,11516070488,15198298704,19730104348,25603499516,33137804244,
    42714330796,54983319726,70337228612,89868125582,114197593794,144609682088,182533078830,
    229434393730,287657657264,359203733056,447029267434,554323251462,684878390602,843337917012,
    1034569995664,1264889738742,1540921530004,1870570081088,2262811204668,2727510227706,
    3276315820370,3921525068684,4677320529028,5559124650026,6583856041046,7770236568552,
    9138034496384,10709166166814,12506374417784,14553926181776,16877456142000,19503283585266,
    22458897175986,25771714148648,29469931896590,33581217407710,38132256728874,43148957662976,
    48655146674704,54672846804542,61220527032350,68313309183042,75962375460032,84173660796670,
    92948033513868,102279752896210,112156965403382,122560561472084,133463694916954,
    144832046256218,156622757192480,168785425769714,181261294536282,193983976393274,
    206879846369778,219867985422860,232861850428206,245769141714348,258493593235550,
    270935614457356,282993457092624,294565237904562,305549429655274,315847239629694,
    325363278191522,334007426969888,341696469961118,348354779579438,353916417281482,
    358325267556220,361536697836726,363518044592436,364248924545434,363722272746484,
    361943518931048,358931485436404,354717251123040,349344064033176,342866525221224,
    335349511859976,326867289397082,317502246640936,307343232290250,296484887403448,
    285025280769720,273065297662214,260706750422638,248050662618806,235196953578052,
    222241731653512,209277576453372,196391752921532,183665147557612,171172642013952,
    158981035709488,147149982128242,135731064726570,124767666437888,114295555475970,
    104342304881504,94928423773352,86066846656498,77764194963070,70020974034288,62831783879784,
    56186954464748,50072018243344,44469172955380,39357516907628,34713670615568,30512680133144,
    26727777293724,23331983248174],
   [20297616065138,17597133719392,15203464061812,13090163701040,11231851989644,9604244708490,
    8184042965712,6949983808584,5881577068186,4960268788188,4168927369330,3491520413204,
    2914324175304,2424145481982,2009494283010,1660180571998,1366879150196,1121741151442,
    917421417788,747927930748,607654767386,491868039702,396870526920,319018650948,255566045494,
    203793153336,161711342852,127695860370,100150534136,77955195038,60170226676,45746112982,
    34533095688,25539403450,18397595498,12963062116,8682183900,5567532106,3130340178,1483381980,
    521428598]]
private def rkmC_w1024_s1a_5 : List ℤ := pzigCat
  [
   [287563990,568674622,1071565944,1497145002,2150294450,2992687736,4054605794,5503552320,
    7173781354,9530926346,12469180040,16289587930,21335867436,27758677854,36103484434,
    46525341890,59894776188,76797295448,97990497334,124744387780,158124577978,199851310132,
    251474304464,315368444738,394249621964,490894421926,609079161656,752841951704,927365404964,
    1138193189440,1391794311230,1695990045920,2059187546104,2491293808498,3003029352732,
    3606829798384,4316625323564,5147471850700,6116418072126,7241568522070,8543166027502,
    10042629872652,11763058683058,13729002446418,15966219007460,18501736616280,21363477597034,
    24579833749392,28179739826080,32191694577696,36643988998860,41563762066080,46976291592738,
    52905054669772,59370102171406,66388643680204,73973376998552,82132044423976,90867341672962,
    100175070853168,110045079647770,120459381419900,131392255094962,142810317907660,
    154671195629930,166924836085364,179512341457976,192366759468356,205413514781894,
    218570431949526,231749178082802,244855329724980,257790173103118,270451192756338,
    282733697584846,294532445392482,305742301567398,316261026798612,325989641485314,
    334834669550826,342709412890266,349535284272046,355243241938014,359774899612766,
    363083446401520,365134686023400,365907066146042,365392982393712,363598038720746,
    360541257293760,356255224706926,350784367208128,344185526076866,336525846906612,
    327882275518752,318340440106706,307992166934030,296935619468930,285272383748224,
    273106477322642,260543113398754,247686511732826,234639357662594,221500590912404,
    208365068991148,195321906204992,182453929835168,169836878013900,157538641106614,
    145619242288570,134130587115828,123115638510414,112609734669232,102639749259048,
    93224931467168,84377378210940,76101882350116,68397895213310,61258516689640,54672203268108,
    48623418294676,43092343572398,38056892150308,33492227554240,29371958641136,25668444073224,
    22353272220322,19398220150826],
   [16774780114582,14455463051188,12413163978020,10621932871360,9057352992884,7696200987822,
    6516641582920,5498503650994,4622940558472,3873338186548,3233863886156,2690485319788,
    2230792578004,1843088322368,1517678693506,1245403624074,1018400674198,830007035442,
    674115586738,545719476418,440083588782,353644602360,283151660972,225692632236,179048075198,
    141262831130,110696232166,86299876338,66509346472,50798178114,38392364406,28427003836,
    20691116504,14561098314,9943767210,6400633966,3719959882,1944675776,733670730]]
private def rkmC_w1024_s1a_6 : List ℤ := pzigCat
  [
   [335898480,697874476,1147554226,1827717720,2418572570,3264735172,4434737204,5883881772,
    7915533184,10340441796,13744827160,18101845546,23616917742,30884981396,39987776948,
    51854879284,66797323408,85651023112,109601034770,139559154744,177316307276,224316006326,
    282680159412,354913233694,443833355744,553141926960,686695062004,849512559450,1046929155998,
    1285597964182,1572828177036,1916993375214,2327884787902,2816390614840,3394870782878,
    4077261068776,4878638196416,5816136927914,6908366678640,8175571956060,9639866396190,
    11324573836564,13255093085884,15457764815484,17960539976272,20792371940898,23982493145922,
    27561343434434,31558533019724,36003613802976,40925164809688,46349694491480,52302197980534,
    58804091029904,65873805249908,73525150114618,81766892455664,90602232075192,100027758299542,
    110032962208486,120599901855276,131702303039498,143305544951068,155365987658140,
    167831485988862,180640881266660,193724264191920,207004112593610,220394472625918,
    233803111856822,247131607832472,260276463611124,273131209716684,285586345089164,
    297532308648882,308860165138158,319463393795394,329240066109274,338093398610618,
    345934647297604,352683475391126,358269807621648,362635071538844,365733221169072,
    367531367218584,368010412676754,367165564721888,365006442594474,361556247340106,
    356852403964684,350945018954708,343896245901994,335779688486568,326677995451394,
    316682801971880,305892143373604,294409332250382,282341613595826,269797485691562,
    256886557133282,243716706431438,230393284186348,217017812407404,203686383106192,
    190488912141028,177508441265164,164820056611690,152490701355016,140578249250704,
    129132410447284,118193854637756,107794426152028,97958167932620,88700457931968,80030130804094,
    71948881506478,64452013597490,57529639264188,51166922530634,45344993315746,40041862244630,
    35232220646138,30889422489774,26985001190924,23489661762900,20373970528504,17608058047366,
    15163373613784],
   [13011353490266,11124565893554,9477381123726,8045034506450,6804679575434,5734800709344,
    4815842282616,4029676865182,3359731463056,2791242710500,2310755986310,1906088149312,
    1566892713464,1283422031844,1047628788494,852229149724,690703709072,558001658170,
    449069687038,359976189620,287380209230,228416743552,180720278500,142136734966,110998425508,
    86215671854,66206850854,50383288336,37898263994,27910096984,20185399164,14100138634,
    9522817958,6030247344,3433778334,1750404278,644841606]]
private def rkmC_w1024_s1a_7 : List ℤ := pzigCat
  [
   [245986072,611656112,852930604,1441257960,1936073858,2762901128,3757607274,4944238700,
    6685723486,8955391954,11927417016,15835345658,20799226216,27313031774,35629319302,
    46309471446,60017943574,77423594946,99718725934,127763276448,163076631416,207245901752,
    262354328652,331050343460,415887725778,520757884058,649446220502,806743513282,998611747348,
    1231087913170,1512081780834,1850003995614,2254853395698,2737874272568,3311665882176,
    3990605257788,4790518711798,5728925189404,6825321895120,8100674610056,9578003544234,
    11281878625362,13238618163360,15476212171442,18023705268904,20911647768806,24170844673702,
    27832953622710,31929427224248,36490837237272,41547563803596,47127274777130,53255773068864,
    59955641084578,67245462388228,75139309230162,83645564788324,92766547080410,102497693069726,
    112826335203882,123732111391056,135185603070738,147148268948788,159572479555078,
    172400688192694,185566609235018,198994343121518,212599858711262,226290867908040,
    239968060782624,253526482538414,266856008581716,279843338038008,292373836557560,
    304332044239430,315604751389276,326081952663298,335658497507690,344236725436764,
    351726890500956,358049997459576,363138218136170,366936313216886,369403303777088,
    370512035683724,370250974577030,368623184599792,365647016090196,361355868337314,
    355796962560998,349030825113372,341130235135062,332178604480534,322269259775850,
    311502901286910,299986409921690,287831000034756,275150527136876,262060034884980,
    248672791006814,235100478167796,221450637614162,207825291863402,194320438218622,
    181024546708980,168017858756066,155372123469226,143149434780452,131403191812620,
    120177141484310,109505780689906,99415123284176,89922166337904,81036643633448,72760517610102,
    65089379469150,58013079705920,51515922084356,45578162515048,40176722343430,35285071349134,
    30875132424004,26916993215656,23380107046576,20233343667032,17445602108132,14986679006178,
    12827043997542],
   [10937945864738,9292864227256,7866008832276,6633607884468,5573889684882,4666071225158,
    3891845601186,3234124128858,2677696661156,2209021549104,1815758687938,1487104704608,
    1213627624270,986807084422,799650173362,645477963358,519105770626,415985932690,331844566162,
    263514875360,208383323202,163753974946,128073353580,99371024970,76397439486,58294900060,
    43821049722,32494661170,23582972388,16712621630,11462625804,7351728400,4352270216,2355118754,
    890802016,235583154]]
private def rkmC_w1024_s1a_8 : List ℤ := pzigCat
  [
   [465364798,727398692,1226947908,1688975336,2271672810,3245942462,4419319158,6071397764,
    8240632534,10894903098,14541525108,19216220222,25294301066,33354129394,43601813710,
    56940052912,73850797110,95580008390,123086503460,157785108940,201622088254,256540795366,
    325107274388,410449259394,516106834416,646468499122,806386394932,1001964373528,1240126752824,
    1528502574320,1876744701084,2295073348558,2795606077120,3392165615530,4099512101932,
    4935109274770,5917503065666,7067551843184,8407970540452,9963362252146,11760366439946,
    13827070966798,16193391070152,18890754642100,21951250075426,25408182566800,29294849771970,
    33644376796894,38489444640630,43860792780166,49787670650446,56295891380436,63407915958684,
    71141553107892,79509167634450,88516995948320,98163940202342,108441255151218,119331759926572,
    130808554096636,142835752979746,155367239789104,168346546885306,181707746806188,
    195374066432866,209259901680134,223270705326148,237303939084268,251250179987142,
    264994375231406,278417822848870,291399353063924,303816596786144,315549170409610,
    326479405333186,336495091686768,345490866987740,353370099433714,360047101899274,
    365448195800238,369512956258750,372196166480126,373467566308406,373313147423224,
    371735336967746,368752408075096,364399184932562,358724853644136,351793554749846,
    343682385431632,334479638536520,324284332111556,313203595121618,301350456391808,
    288843195164896,275802173347264,262348808482884,248603143761154,234682414357638,
    220699571801846,206761506004040,192968012308588,179411072840736,166173188302180,
    153327959498806,140938753185868,129058732807466,117731850334304,106991360552492,
    96861832323642,87358788042258,78489093288898,70252482331906,62641824714262,55643763302260,
    49240136551486,43408075017536,38121800311142,33352399422480,29069052999038,25239818481390,
    21831874748280,18812405292360,16149154003034,13810065625016,11765070378496,9984876449282,
    8441681196014],
   [7109921948046,5965553316946,4986281057078,4152130235152,3444265400106,2846398276570,
    2343562622402,1922233965012,1570875334168,1279063208868,1037455251440,838519012038,
    674995357088,541262321746,432386960224,343843613118,272201174474,214486563120,167886258920,
    130780206710,101066371448,77399501616,58765276848,43968704030,32358620074,23475897714,
    16395237790,11133121496,7108786234,4055438110,2037340828,726777888]]
private def rkmC_w1024_s1a_9 : List ℤ := pzigCat
  [
   [271694672,652473398,965362808,1545086182,2261495514,3093919128,4327807474,5894927458,
    7930011616,10657479052,14251438294,19085827662,25332158452,33494468886,44192712252,
    57822111200,75600222238,98163435390,127061055574,163795141598,210087229724,268596814386,
    341994815514,433495622468,547401598948,688094029234,861416766488,1073869704974,1333255940498,
    1648499534738,2029806936020,2489130122888,3039824590278,3696973664622,4477850247658,
    5401232785372,6488241200534,7762359051078,9248416422632,10974134887968,12968649880406,
    15263322740596,17890914793912,20885244809912,24281735329494,28116059104186,32423537402752,
    37239439299046,42597213068680,48528944660842,55063216429076,62224796317506,70034291446350,
    78506158562556,87648161484430,97460981419850,107936356453948,119057161716950,130796475166480,
    143116673554602,155969646630838,169295644470454,183024715244348,197075480033376,
    211356315800976,225766510066664,240196170019152,254528227508662,268640034433856,
    282404057363732,295691081392224,308370846261988,320314890558164,331398829939674,
    341503906910066,350519396362128,358344850473714,364891409118338,370084268241008,
    373863177916832,376184501582628,377021394167458,376364417223756,374222221601658,
    370620791001874,365602831366650,359227973582210,351570015320694,342716764587124,
    332767912745826,321832844301720,310029437945892,297481412128052,284315732387360,
    270661992516468,256648769866148,242402566746622,228045769487338,213694677699920,
    199458721269778,185438813502786,171725890668556,158401719196830,145536735835498,
    133190740620362,121412944997692,110241535088502,99704625925156,89820650498276,80598286021604,
    72038809679742,64135394478064,56874706024156,50238040787576,44201524263548,38737587380940,
    33815986775462,29403565779218,25466603182238,21970180647138,18879215459634,16159430663480,
    13777060306390,11699596921170,9896524041036,8338224991558,6997681322402,5849601420710],
   [4870562717134,4039584597164,3337376067308,2746363394744,2251442458918,1838475923530,
    1495492238978,1211919575680,978226040148,786511485158,629928191936,502264756746,398903344826,
    315312058916,247955394544,194012089880,150805628382,116360450724,89195543794,67579034294,
    50711853290,37499424244,27110038312,19146648280,13019970294,8326502112,5011975538,2742796350,
    1016115622,259196354]]
private def rkmC_w1024_s1a_10 : List ℤ := pzigCat
  [
   [306059224,629837466,1088980294,1659961290,2290896450,3295246846,4538744318,6168117926,
    8495853524,11426208026,15382478602,20809919654,27756503454,37039546374,48860950524,
    64343859146,84461720066,110147210714,143168397180,185431183090,239067334890,306787650868,
    391752493430,498439122102,631127371582,795564737378,998698057388,1248133182304,1553180096758,
    1924563278694,2374098995758,2916152703134,3566410542604,4342846719838,5265504332212,
    6356637980384,7641004426762,9145569303146,10899368152426,12934079638196,15282921572896,
    17981384267254,21066004790710,24574570027296,28545661222240,33017436489304,38027579414626,
    43612729984752,49806218629734,56638870906746,64136825875432,72320721665842,81205233990494,
    90797177361394,101094782798356,112087407601234,123753295739638,136060352305882,
    148964488796874,162409444461242,176327264302198,190637670882006,205248600680010,
    220057458414694,234950825473730,249807233759206,264497465107020,278886499145156,
    292836275887126,306206902302352,318858987525808,330656957473934,341470161176216,
    351176584271282,359664136812426,366832946241038,372598074014354,376890339084562,
    379657738101340,380867456963640,380505057825052,378576071356874,375105161455014,
    370135512945738,363728644704514,355962425751332,346929417867096,336736115271872,
    325499402094130,313345521239816,300407241782952,286821201554844,272726306286386,
    258260879761206,243560115065188,228755185924432,213970037932008,199320871020412,
    184914592572550,170847305306502,157204260867724,144059070059148,131472930768614,
    119495869085782,108165787989424,97509626988386,87544146348000,78275826350448,69702803631362,
    61815195933258,54596258435688,48023442079578,42069607639178,36703274285586,31890796736744,
    27596201000564,23782306689742,20411899808240,17447588800882,14852598592482,12592065463276,
    10631782817518,8939874005354,7486631646592,6243886037572,5186171842208,4290170209878,
    3534581675044],
   [2900249857182,2370317062504,1929279095038,1564138697496,1263019658574,1015583504678,
    813426459094,648885240944,515163810738,407283023294,320374796370,250664736098,195095465276,
    150839690714,115803200472,88196050420,66396837002,49281455180,36196160714,25850793222,
    17957724074,12085531066,7599170248,4368531892,2234375382,785792864]]
private def rkmC_w1024_s1a_11 : List ℤ := pzigCat
  [
   [488193548,786416284,1373971902,1980604288,2688606244,3807506198,5286211250,7344644612,
    10255283526,13798462242,18843330366,25475567844,34014497532,45419126258,60340329754,
    79767721774,105199454406,137805826892,179904305914,233622173690,301856130418,388369362484,
    497215671990,633602998602,803913460896,1015060876052,1276040758932,1596609576334,
    1988442757362,2465283726898,3042349132164,3737302802742,4570249466926,5563095818936,
    6741184794342,8131805552336,9764893667166,11673102629208,13891143491230,16456206384690,
    19407386721574,22784690614860,26630061251170,30985137420474,35891245168032,41388830054488,
    47515802999200,54307021432440,61793126195254,69998775516386,78942789538640,88635422237140,
    99077900645770,110261641146402,122166466804232,134760291601794,147998390481646,
    161822255549314,176160530220218,190928074255526,206026596679268,221346168238620,
    236764800444830,252151163999130,267365444976288,282261587268640,296689628307784,
    310498033480180,323535942412252,335656767451442,346720016015796,356594422416338,
    365160639212112,372313227907632,377963109064302,382039723660056,384491495215890,
    385288104723762,384420516230052,381900693340774,377762659884536,372060167000204,
    364866512898416,356272862574490,346385953897588,335326059902998,323225286303854,
    310223687652344,296467576793110,282106628736272,267290611972242,252167587816560,
    236881566379218,221569380346684,206360181922730,191372851238350,176714881867512,
    162482225265246,148757292306696,135609760804318,123096243387048,111260198054752,
    100132674793448,89733603511260,80071299118886,71144490804600,62943401924746,55450103584816,
    48640670653032,42485544007804,36951073207502,32000593071274,27595333707114,23694802469754,
    20258925105806,17247488016068,14620794712522,12341306977834,10372735594728,8680846488966,
    7233944273722,6002696744582,4959664438828,4080641793752,3343231390810,2727376648598,
    2215806176294,1792680472878],
   [1444183795456,1158559227894,925531518670,735941009210,582738093130,459251774554,360028280004,
    280898623028,217900916852,167873154856,128453186378,97502080944,73058600770,54236247314,
    39596123332,28238073758,19690220286,13195272202,8271493254,4811744670,2487563538,865901374,
    207559686]]
private def rkmC_w1024_s1a_12 : List ℤ := pzigCat
  [
   [246752982,448816974,766748388,1211790466,1667143168,2598235250,3686437826,5239527014,
    7453830354,10219771780,14070203846,19281021294,26081306418,35308549946,47545973342,
    63759664782,85207084250,112847726438,149063525064,195802596490,255818534892,332642848568,
    430356691244,554047331252,709882231904,904944838174,1148161538572,1449540730220,
    1820891415110,2276264928948,2831662527328,3505373923842,4318487727888,5294484629768,
    6459838270912,7844023948300,9478730394296,11399420802174,13643554668600,16251403514636,
    19265605188958,22730198989394,26690499991018,31192506371390,36281307307944,42001200708248,
    48393803376442,55496789232234,63343313939190,71960191537946,81366212248092,91571713015210,
    102576181365256,114367274846926,126920600494748,140196974230508,154143336037188,
    168691583815438,183758226782064,199245171957296,215039998750462,231016622396308,
    247037318024120,262953965504054,278609935483056,293843575686446,308489385717076,
    322382169252470,335359702370910,347265502147398,357952428134942,367285817578840,
    375145520067242,381429134837818,386054522327314,388960497074684,390109499770682,
    389487326580096,387103830863484,382992786672274,377210826059786,369836130185730,
    360967344509300,350720487725826,339226543066676,326629979208262,313083882291450,
    298747892455510,283785305152026,268359498928072,252631039083468,236755831228656,
    220881652647884,205146535055854,189677582298516,174588225689120,159978635741556,
    145934600893006,132526913032436,119811811326686,107831805210280,96615148968188,
    86177764462372,76524266132680,67648100696660,59534145830022,52159279964188,45493673779256,
    39502498725040,34147274860200,29386012857250,25175558076356,21472052098180,18231277473892,
    15410404875538,12967835168162,10863456784636,9059913789662,7522051254238,6217375804384,
    5116028880614,4191278195844,3418409312456,2775719248406,2244130585726,1806257249430,
    1447321779016,1154687067502],
   [916986519054,724792263774,570221420076,446543742906,347620936198,269180942588,207220923546,
    158262485282,119985191918,90195751838,66900757764,48876989212,35157235334,24695566374,
    16638920918,10901973608,6604525694,3485791312,1569451932,496135444]]
private def rkmC_w1024_s1a_13 : List ℤ := pzigCat
  [
   [266187190,473590198,962309802,1536082714,2293394114,3484787766,4940359074,6874904578,
    9672041236,13426790072,18502007456,25561427608,34794613208,47486096310,64331315352,
    86470846182,115849769888,154145825728,203971988436,268628810220,351825332596,458345227614,
    594252090466,766118766672,982698339274,1253772495474,1590999486034,2008547354074,
    2522465206576,3151537408808,3917269364888,4843955896936,5959027565940,7293477440050,
    8880811596840,10758535847196,12966991315616,15549248753394,18551496161468,22021687355298,
    26009215098208,30564444675704,35737434576470,41576515838870,48128188047112,55434358287406,
    63531914521604,72450873783764,82212331770348,92827615544354,104296214225596,116604074104886,
    129723001481554,143609499205632,158202719247364,173425908530936,189185072076550,
    205369154185150,221851747354214,238491686775654,255134397645672,271614776312678,
    287759447884280,303389182475766,318323300253368,332381562459110,345388683042306,
    357178145324376,367594993775274,376499552295078,383771145622244,389309822227696,
    393039084099706,394908128695088,394891964114860,392992551009006,389239171263910,
    383686349410582,376414094251034,367525100404258,357142336912138,345406561204084,
    332473142989114,318508244603064,303685713241310,288183737302000,272180609413160,
    255851949802200,239367927919188,222889353987404,206566763340358,190537520974536,
    174924335917808,159834427428694,145359123334428,131573001911204,118534346553186,
    106286131286202,94855818607138,84256989738910,74491339272614,65548494553030,57408626055294,
    50043826611338,43419425244128,37495103506232,32227300957564,27569859211172,23474695026222,
    19894032106534,16780577576266,14087781385974,11771624215820,9790186401786,8104109458260,
    6676892234406,5475569116034,4469529261598,3631257298292,2936683594010,2363970145790,
    1894009273348,1510536330482,1199120495480,947259684782,744692983622,582543680004,
    453353405110],
   [350715526954,269881879836,206286736308,156322830976,117562077160,87587479702,64317439616,
    46479355980,33013194746,22811619308,15116660414,9548140444,5677054290,2926055930,978649408,
    222085642]]
private def rkmC_w1024_s1a_14 : List ℤ := pzigCat
  [
   [506092730,1057240536,1593205008,2524901860,3712738506,5170510014,7474297034,10527405974,
    14755485996,20664643594,28745155640,39689709720,54651489490,74440115288,100850374236,
    135921670558,181978567922,242599918416,321498092002,423507372986,554865555602,722775759462,
    935775774118,1205059357996,1542960095282,1964371692468,2487287178134,3131879132520,
    3921607043796,4883563164498,6047889924698,7448677918210,9123773003970,11114492147326,
    13465962682252,16226829355806,19447838661876,23182964575586,27487112742812,32415496175706,
    38023445034318,44363932225350,51486426804964,59435668273000,68249309437934,77956422461918,
    88575560555226,100112817317776,112559656333798,125892478927492,140069849678228,
    155032261653648,170701546932314,186979745901254,203750058169142,220877576041934,
    238210077341606,255580277889180,272808200976230,289703898067634,306070438123396,
    321708692906416,336419840557100,350010520614084,362297182891188,373109374879734,
    382294316042442,389720645083360,395280873016020,398894154207576,400508734414688,
    400102798579088,397684424870146,393292829522036,386995764127160,378888274773808,
    369091001912088,357746515964528,345015713062726,331074662810696,316110506766572,
    300316603161410,283889399735948,267024173148492,249910648914950,232730415116824,
    215654213964478,198838148432690,182423242921642,166533231049042,151273471096604,
    136730900026414,122974228584356,110054161561112,98004009251832,86841634070842,76570348879186,
    67180150875154,58650380607784,50950885822764,44043507839392,37884468169426,32426054016990,
    27616928968078,23404851710226,19737189621698,16562063647022,13828990855752,11489842099432,
    9499478418064,7815203489186,6397770101654,5211885301696,4225144481846,3408347200092,
    2736057363828,2185816667388,1737557467160,1374396100422,1081724980498,847238301714,
    659959769918,511193849028,393908682834,301631685966,229275355632,173054431334,129538292556],
   [95841802336,69989962812,50435229510,35671708066,24490212588,16175303888,10225827818,
    6045783326,3048022768,987730238,216568618]]
private def rkmC_w1024_s1a_15 : List ℤ := pzigCat
  [
   [213896091,57526734,309309672,825266942,1430825962,2084444882,3195867022,4514599570,
    6523348602,9525689366,13704532200,19409900108,27506344186,38446845182,53256925376,
    73574669172,100844164602,137447629238,186383680006,250959579866,335957379516,446787162046,
    590405927356,775347882256,1012068453320,1312789833708,1692688223822,2169609203880,
    2764009944390,3500282148302,4406240061860,5513443544470,6858219302924,8480647013424,
    10425256016822,12740846828478,15480252973618,18699335249032,22457315188022,26815162354766,
    31834328925162,37576666926276,44101695570902,51465048762056,59717204145290,68900802955064,
    79048150735278,90180033024766,102302752141598,115405976583934,129461260650258,
    144420677041632,160214342959704,176751173250992,193918181884386,211580001287490,
    229581352502822,247748050524668,265888998262004,283799817412320,301266163644720,
    318067723223918,333982920991972,348794153518536,362291779260264,374279695400580,
    384580112630878,393037748445424,399523214243576,403937540125986,406213518840384,
    406317556032028,404251475425274,400051230046010,393786218552908,385557768335748,
    375496020651094,363756633681414,350516820003862,335971234200460,320326594989520,
    303797240891720,286600541417312,268952228592170,251061161130006,233127009530748,
    215335971760226,197857541532828,180843342337088,164425141686828,148713737109642,
    133798768105808,119749343018792,106614556766290,94423994822720,83190046987830,72909903731604,
    63566504855348,55130986163082,47565476298884,40824137790090,34855299856720,29603674366710,
    25012304554932,21022639630184,17577049816272,14619519928020,12096242550506,9956415673636,
    8152414037410,6640658277308,5381384953318,4338247961794,3479152548290,2775983540886,
    2203552674160,1739893352186,1366590569918,1067869781418,829945915566,641310032148,
    492656015794,376260806988,285391927330,214848149370,160220594180,118494740738,86709929072],
   [62353124640,44045175914,30571403464,20552889606,13072648176,7736515664,4187270278,1935283946,
    589263606]]
private def rkmC_w1024_s1a_16 : List ℤ := pzigCat
  [
   [510672598,856983234,1292066900,2071682346,3120214596,4687760258,7197077132,10466357134,
    15147935794,21821402868,31021509448,43755730106,61527076862,85852230798,118937109564,
    164029618782,224306995230,304391778370,410524686392,549564921326,730796559188,965503579746,
    1267030042858,1651676786888,2139252720980,2752416743254,3518174112000,4467853230136,
    5637239308684,7066960305944,8802930503976,10895866802184,13400973887480,16378538507454,
    19892291896500,24008922812596,28797775497426,34328061770770,40668152628426,47883685183178,
    56034850738656,65173955693714,75343709562598,86573659118418,98877993579626,112252813582204,
    126673895415666,142094417769712,158443466820034,175625678991890,193519691554510,
    211979015045128,230833641127458,249890839736612,268938529080354,287749119123602,
    306083116481510,323694153816238,340334952232834,355762662580734,369744549252516,
    382063748026282,392525814083068,400962522234118,407237003192774,411247645630444,
    412930614792872,412260957331314,409254004540910,403965066885066,396486429731502,
    386945790612978,375502940490608,362344208468960,347678043790104,331729858017652,
    314735959742176,296937886417860,278576845742650,259888724551240,241099079899638,
    222418731436926,204040742081134,186138076083258,168860434865712,152333936759912,
    136660650241072,121918910332646,108163322015694,95427133176866,83724019890272,73049076091438,
    63382024087822,54689791589012,46928452303872,40045712391102,33983137864850,28678618893566,
    24068273364988,20087347149536,16671905792276,13760661398608,11295246434542,9220391430368,
    7485071127134,6043014310418,4852168109880,3874593617110,3076900578646,2430077580808,
    1908777004640,1490975084628,1157999562544,894252578790,686595331784,523924354928,
    397084063246,298748838952,223049528646,165150330000,121047540734,87565688096,62322417892,
    43531802374,29765367188,19720946920,12523214316,7042290310],
   [3318367986,1291116496,350009970]]
private def rkmC_w1024_s1a_17 : List ℤ := pzigCat
  [
   [204050488,569475274,900030042,1578228988,2722733588,4172886270,6441197726,9619637026,
    13975222098,20435550896,29612340000,42611076272,60974839726,86601429690,121927107636,
    170189196556,235844809114,324062610886,441832040138,598229788124,803986677042,1072480151220,
    1420469000038,1867429007870,2437292657494,3158304253488,4063492276094,5191030019738,
    6585091008932,8295442528176,10377363045374,12892362339966,15907205443248,19493247561268,
    23725756538716,28682710806916,34442618529238,41082703343560,48677516150644,57295132402780,
    66994146033874,77821849567698,89809815376376,102970645585174,117295818658418,132752520469060,
    149280675058240,166792355280460,185170048786172,204266626692232,223905609215878,
    243883652772562,263973083907228,283925194026836,303475562789438,322349599479028,
    340268673762816,356956532358562,372146975563508,385590934018050,397062291144894,
    406365123340770,413339460411014,417864728866216,419863852491594,419305945951598,
    416206392956926,410626238839666,402670521703634,392484972977336,380251512303876,
    366182756515160,350516191808462,333507738900182,315424353960174,296537246654116,
    277116049345816,257422385757270,237703692273438,218189081208074,199086075537036,
    180577082445234,162817160885146,145933719383628,130026588860396,115168104316824,
    101404498179944,88758286416376,77230747032822,66803946929950,57444081210910,49104232940832,
    41727892858700,35250604609284,29603201673428,24714010224134,20510692610814,16922188994544,
    13879398078292,11316696413790,9173110653864,7392094862144,5921986215706,4716545886456,
    3734544743636,2939640733966,2300453601904,1789846892796,1384270179230,1063900126338,
    812555382018,616796322540,465149847370,348100147316,258226744574,189829385310,138276812374,
    99645515092,70741662220,49176539010,33252518234,21716851878,13560839360,7944687060,
    4201047834,1839468230,520097956]]
private def rkmC_w1024_s1a_18 : List ℤ := pzigCat
  [
   [432846236,1044666844,1840840304,2926650232,4704037564,7075040290,10483865526,15811305692,
    23669112760,34837045006,51259997666,74430961768,106752367058,152021544132,214511823702,
    299960017004,416115754638,572717214212,781524603910,1057554289198,1419561118040,
    1890019804954,2496288803858,3271071332814,4252723523532,5485835450056,7021832972256,
    8919367607914,11243607260006,14066381624216,17466276659510,21526614072174,26334357297944,
    31979308369256,38550973251520,46135772771210,54814763957420,64659609734128,75728468090770,
    88062676172990,101682846826204,116584744163700,132735865505876,150072763481744,
    168498807991252,187882452198982,208056964344096,228821895162900,249944918348298,
    271164909704642,292197042857042,312739264868908,332478253103030,351097750164362,
    368287047765434,383749788988796,397211240193468,408427463223078,417192889909752,
    423345863973154,426773644107440,427415969144304,425267370890034,420376377374862,
    412843584652744,402819174596640,390497447027460,376110348891742,359920686937900,
    342214118871536,323291037087748,303458154832874,283020224767842,262273146289780,
    241497295778744,220951174871282,200867211306914,181448846217058,162867830552294,
    145263027720926,128740885694534,113376373073410,99214612621042,86273616048190,74547303943976,
    64008606197098,54613170952906,46303170978638,39010409347540,32659200957950,27169615892458,
    22460390337732,18450766612630,15061812437170,12218009828136,9848798263998,7889305834214,
    6280342876520,4968389466826,3905861049936,3051236260966,2368680146308,1827355620894,
    1400853392780,1066874751884,806954953526,606015721646,451776557544,334208398884,245150634922,
    178062506450,127808742610,90419701298,62839874262,42709724050,28205503758,17927432438,
    10811811510,6051487512,3025385694,1246346550,333487772]]
private def rkmC_w1024_s1a_19 : List ℤ := pzigCat
  [
   [407757398,1009554028,1632886620,2481209996,4023894296,6242392752,9654356668,15227573956,
    23493445514,35393402644,52862660840,78149099830,114270138080,165496253482,237534669916,
    337454703148,474827135218,661826385018,914038094388,1250527729212,1695412379228,
    2278063010860,3033646367050,4004275666854,5239777427964,6797951356924,8744329109256,
    11153289757284,14107410005086,17696086720754,22015385095860,27166303516406,33252050954938,
    40375187356292,48634564399832,58121478998658,68914468304654,81075083949404,94643758122412,
    109633916144348,126027324841720,143770982734276,162773548686580,182902714425052,
    203984408567894,225803424333762,248105690823548,270601814319772,292972330966764,
    314875231548330,335954264795860,355847785820068,374199363675354,390668788116588,
    404941962992490,416740720369812,425832400918356,432037368507100,435234488660448,
    435365280973858,432435872858480,426516253700036,417737539310282,406287342359868,
    392403046401334,376363689147774,358480992318984,339089374082814,318535473451952,
    297168296076762,275330100412068,253347621813242,231524265841128,210134248364082,
    189418438787902,169581123719800,150787937586598,133165729233336,116804126077086,
    101757780086946,88048960487756,75670998264404,64592705925274,54763027248752,46115205047698,
    38570541203302,32042164942086,26438770649460,21667839276868,17638047012740,14261058136820,
    11453046636058,9136010865938,7238681722954,5696890754250,4453517963114,3458264048842,
    2667390058656,2043399247876,1554580512194,1174405231226,880860490204,655815041712,
    484475722208,354885669568,257554625242,184868332300,131135330430,91466331966,62737077716,
    42010645078,27183764590,17009554134,10254471640,5778933896,2876177938,1154580100,296468946]]
private def rkmC_w1024_s1a_20 : List ℤ := pzigCat
  [
   [338028104,465477670,897451680,1582683942,2626672208,4474339810,7540354314,12126001032,
    19016672788,29763774028,45948112302,69715304230,104775480388,155760267942,228562005608,
    331763530334,476579488004,677005579180,951248682712,1322628119996,1820088169810,
    2479177394684,3343244475570,4464426975826,5903972562028,7732587927882,10031421378644,
    12892067514392,16415226003682,20709740171598,25891320392498,32079426697800,39393602285664,
    47949906552316,57855975465870,69205044109466,82070354259056,96499378187918,112507387530436,
    130071604841752,149126479442470,169559701137596,191209499170044,213863946106464,
    237262129796596,261097304647266,285022455156162,308657936399968,331600738772656,
    353435588647820,373747591722144,392135232864036,408223181449348,421675097754782,
    432205740110102,439590945572086,443675112238806,444376676579876,441691218879726,
    435691185061494,426522292340014,414397687431798,399590264386962,382422728177254,
    363255666076554,342474940970736,320479414461108,297668992231894,274432911982816,
    251139067600388,228125266093772,205692738655936,184101164560438,163565560945044,
    144254485327246,126291231475142,109755455119652,94687494611618,81091466060978,68940826395418,
    58183225868624,48745957547702,40541729202438,33472691619120,27435023465152,22322887334952,
    18031186835860,14458636340228,11509839003140,9096112167794,7136532938860,5558692587506,
    4298433563806,3299742940026,2514468677378,1902113124168,1428106166938,1064142066768,
    786587370350,576635881954,419180297472,301718866672,214663581240,150793895196,104336572968,
    70827818916,47035052114,30458671850,19177866484,11409700716,6506982734,3346152814,1356778206,
    339660526]]
private def rkmC_w1024_s1a_21 : List ℤ := pzigCat
  [
   [265702004,710339152,1246913672,2369828666,4360081648,7351488088,12195868000,20154140476,
    32457302658,51183012882,79821256406,122965420710,186741070952,279751071696,413497499372,
    603068250320,868462417168,1235599254878,1737126694256,2413744659300,3315590046246,
    4503241957474,6048695478890,8036195102866,10562503683148,13736717001472,17679505884176,
    22521242172846,28399135027918,35453747131330,43824419541166,53643262994734,65028475981812,
    78077409084548,92858909883436,109405022738824,127703528842470,147691615699324,
    169250726228154,192202213686828,216306329891254,241263385739806,266718518511544,
    292267310272826,317466153624892,341844131118730,364918015864950,386207410841888,
    405250922451078,421623602699822,434952451876012,444930769282272,451329350953122,
    454005042637022,452906911859520,448077326615840,439649342185886,427840869730768,
    412945316021192,395319994195686,375372412667580,353543906343478,330294472735686,
    306087027830458,281373379571374,256580295620588,232099313218858,208277133630492,
    185409722071186,163739442239726,143453049372092,124682928262712,107510057155782,
    91968516679904,78051345530070,65716711150444,54894170085884,45492169188484,37403059136320,
    30509758623056,24690545840100,19823976036912,15791585204822,12480456439802,9786195205056,
    7613536729388,5876723534738,4500516316758,3419427346730,2577508566114,1927191349264,
    1429443490866,1051486265004,766732753500,554085089246,396424512738,280409486768,195834186098,
    134885828514,91201425026,60612943862,39335319152,24763896734,15081058384,8703675208,
    4554909174,2044344118,727270420]]
private def rkmC_w1024_s1a_22 : List ℤ := pzigCat
  [
   [650908092,1612852872,3180480582,5795497840,10009276602,17132094964,28883816146,47991644194,
    77905391674,124278166334,194707494648,299843279934,454200432148,677649485008,996531429140,
    1444427899266,2064639628230,2911451406080,4051558938834,5565429695866,7548550741602,
    10112653233002,13384631522514,17505531071602,22629011135722,28917764560086,36538395220170,
    45655338823612,56423069534746,68978553788784,83430241310524,99848378182360,118254976099702,
    138615005649372,160827647744960,184720377782772,210045938104452,236482254473020,
    263636873500606,291053293258466,318222396114410,344598092803556,369614819833968,
    392707037330768,413331014674940,430985208841170,445231826649970,455714027603284,
    462171076829650,464448660316096,462504974122816,456412340228696,446352697334834,
    432608605565116,415550273449856,395619428135412,373311342215242,349153587919978,
    323687208167280,297446851529098,270943243520128,244647958871018,218982143562706,
    194307150495028,170918287125840,149044164086528,128846934101242,110425942650560,
    93823194976622,79030854273172,65998098076166,54640886911126,44849661038684,36496822675692,
    29444888078364,23551936349340,18677065058950,14684502632142,11446927419566,8846792263576,
    6778907074444,5149946684344,3878759190818,2896229310534,2143924732932,1572942358094,
    1143759029058,823755910948,587335260936,414221800436,288541879212,198296243940,134316013706,
    89283319830,58281435476,37084754694,22855693726,13564823610,7481604370,3828884584,1503353110,
    347118608]]
private theorem rkmWC_w1024_s1a_0 : wSlChk 17 100000000 1024 rkmHbF_w1024_s1a
    320 rkmXsWin_w1024_s1a_in 345 rkmC_w1024_s1a_1 3557280253 = true := by decide +kernel
private theorem rkmWC_w1024_s1a_1 : wSlChk 17 100000000 1024 rkmHbF_w1024_s1a
    345 rkmC_w1024_s1a_1 371 rkmC_w1024_s1a_2 3366970861 = true := by decide +kernel
private theorem rkmWC_w1024_s1a_2 : wSlChk 17 100000000 1024 rkmHbF_w1024_s1a
    371 rkmC_w1024_s1a_2 397 rkmC_w1024_s1a_3 3528033916 = true := by decide +kernel
private theorem rkmWC_w1024_s1a_3 : wSlChk 17 100000000 1024 rkmHbF_w1024_s1a
    397 rkmC_w1024_s1a_3 422 rkmC_w1024_s1a_4 3405594026 = true := by decide +kernel
private theorem rkmWC_w1024_s1a_4 : wSlChk 17 100000000 1024 rkmHbF_w1024_s1a
    422 rkmC_w1024_s1a_4 448 rkmC_w1024_s1a_5 3585909236 = true := by decide +kernel
private theorem rkmWC_w1024_s1a_5 : wSlChk 17 100000000 1024 rkmHbF_w1024_s1a
    448 rkmC_w1024_s1a_5 474 rkmC_w1024_s1a_6 2968974341 = true := by decide +kernel
private theorem rkmWC_w1024_s1a_6 : wSlChk 17 100000000 1024 rkmHbF_w1024_s1a
    474 rkmC_w1024_s1a_6 499 rkmC_w1024_s1a_7 2985672030 = true := by decide +kernel
private theorem rkmWC_w1024_s1a_7 : wSlChk 17 100000000 1024 rkmHbF_w1024_s1a
    499 rkmC_w1024_s1a_7 525 rkmC_w1024_s1a_8 3495254765 = true := by decide +kernel
private theorem rkmWC_w1024_s1a_8 : wSlChk 17 100000000 1024 rkmHbF_w1024_s1a
    525 rkmC_w1024_s1a_8 550 rkmC_w1024_s1a_9 3258386542 = true := by decide +kernel
private theorem rkmWC_w1024_s1a_9 : wSlChk 17 100000000 1024 rkmHbF_w1024_s1a
    550 rkmC_w1024_s1a_9 575 rkmC_w1024_s1a_10 3305967812 = true := by decide +kernel
private theorem rkmWC_w1024_s1a_10 : wSlChk 17 100000000 1024 rkmHbF_w1024_s1a
    575 rkmC_w1024_s1a_10 600 rkmC_w1024_s1a_11 3093098123 = true := by decide +kernel
private theorem rkmWC_w1024_s1a_11 : wSlChk 17 100000000 1024 rkmHbF_w1024_s1a
    600 rkmC_w1024_s1a_11 623 rkmC_w1024_s1a_12 3141455159 = true := by decide +kernel
private theorem rkmWC_w1024_s1a_12 : wSlChk 16 100000000 1024 rkmHbF_w1024_s1a
    623 rkmC_w1024_s1a_12 646 rkmC_w1024_s1a_13 2865832583 = true := by decide +kernel
private theorem rkmWC_w1024_s1a_13 : wSlChk 16 100000000 1024 rkmHbF_w1024_s1a
    646 rkmC_w1024_s1a_13 669 rkmC_w1024_s1a_14 3183589803 = true := by decide +kernel
private theorem rkmWC_w1024_s1a_14 : wSlChk 16 100000000 1024 rkmHbF_w1024_s1a
    669 rkmC_w1024_s1a_14 688 rkmC_w1024_s1a_15 2889099647 = true := by decide +kernel
private theorem rkmWC_w1024_s1a_15 : wSlChk 16 100000000 1024 rkmHbF_w1024_s1a
    688 rkmC_w1024_s1a_15 711 rkmC_w1024_s1a_16 3472715996 = true := by decide +kernel
private theorem rkmWC_w1024_s1a_16 : wSlChk 16 100000000 1024 rkmHbF_w1024_s1a
    711 rkmC_w1024_s1a_16 731 rkmC_w1024_s1a_17 2749574459 = true := by decide +kernel
private theorem rkmWC_w1024_s1a_17 : wSlChk 16 100000000 1024 rkmHbF_w1024_s1a
    731 rkmC_w1024_s1a_17 752 rkmC_w1024_s1a_18 2261414734 = true := by decide +kernel
private theorem rkmWC_w1024_s1a_18 : wSlChk 16 100000000 1024 rkmHbF_w1024_s1a
    752 rkmC_w1024_s1a_18 771 rkmC_w1024_s1a_19 1955933599 = true := by decide +kernel
private theorem rkmWC_w1024_s1a_19 : wSlChk 16 100000000 1024 rkmHbF_w1024_s1a
    771 rkmC_w1024_s1a_19 789 rkmC_w1024_s1a_20 2444898955 = true := by decide +kernel
private theorem rkmWC_w1024_s1a_20 : wSlChk 16 100000000 1024 rkmHbF_w1024_s1a
    789 rkmC_w1024_s1a_20 808 rkmC_w1024_s1a_21 2242078965 = true := by decide +kernel
private theorem rkmWC_w1024_s1a_21 : wSlChk 16 100000000 1024 rkmHbF_w1024_s1a
    808 rkmC_w1024_s1a_21 827 rkmC_w1024_s1a_22 2108730174 = true := by decide +kernel
private theorem rkmWC_w1024_s1a_22 : wSlChk 16 100000000 1024 rkmHbF_w1024_s1a
    827 rkmC_w1024_s1a_22 843 rkmXsWin_w1024_s1a_out 2046478936 = true := by decide +kernel
private theorem rkmHbEq_w1024_t1 : rkmAllTrueF [
  muxIntListEq rkmHbF_w1024_s1a rkmHbWin_w1024_s1a
  ] = true := by decide +kernel
private theorem rkmWinIterF_w1024_s1a :
    RkmWinIterSound 380 1024 rkmHbF_w1024_s1a 320 rkmXsWin_w1024_s1a_in
      843 rkmXsWin_w1024_s1a_out 67912944915 :=
  rkmChS 380 67912944915 (rkmChS 364 65866465979 (rkmChS 348 63757735805 (rkmChS 332 61515656840
    (rkmChS 316 59070757885 (rkmChS 300 57114824286 (rkmChS 284 54853409552 (rkmChS 268
    52103835093 (rkmChS 252 48631119097 (rkmChS 236 45742019450 (rkmChS 220 42558429647 (rkmChS
    204 39692597064 (rkmChS 187 36551141905 (rkmChS 170 33458043782 (rkmChS 153 30152075970
    (rkmChS 136 26893689428 (rkmChS 119 23398434663 (rkmChS 102 20412762633 (rkmChS 85
    17443788292 (rkmChS 68 13857879056 (rkmChS 51 10452285030 (rkmChS 34 6924251114
    (wSlChk_sound rkmWC_w1024_s1a_0) rkmWC_w1024_s1a_1 rfl rfl) rkmWC_w1024_s1a_2 rfl rfl)
    rkmWC_w1024_s1a_3 rfl rfl) rkmWC_w1024_s1a_4 rfl rfl) rkmWC_w1024_s1a_5 rfl rfl)
    rkmWC_w1024_s1a_6 rfl rfl) rkmWC_w1024_s1a_7 rfl rfl) rkmWC_w1024_s1a_8 rfl rfl)
    rkmWC_w1024_s1a_9 rfl rfl) rkmWC_w1024_s1a_10 rfl rfl) rkmWC_w1024_s1a_11 rfl rfl)
    rkmWC_w1024_s1a_12 rfl rfl) rkmWC_w1024_s1a_13 rfl rfl) rkmWC_w1024_s1a_14 rfl rfl)
    rkmWC_w1024_s1a_15 rfl rfl) rkmWC_w1024_s1a_16 rfl rfl) rkmWC_w1024_s1a_17 rfl rfl)
    rkmWC_w1024_s1a_18 rfl rfl) rkmWC_w1024_s1a_19 rfl rfl) rkmWC_w1024_s1a_20 rfl rfl)
    rkmWC_w1024_s1a_21 rfl rfl) rkmWC_w1024_s1a_22 rfl rfl
/-- Certified `w1024_s1a` partial walk (`380` substeps). -/
theorem rkmWinIterSnd_w1024_s1a :
    RkmWinIterSound 380 1024 rkmHbWin_w1024_s1a 320 rkmXsWin_w1024_s1a_in
      843 rkmXsWin_w1024_s1a_out 67912944915 :=
  rkmSubstHb (rkmWP0 rkmHbEq_w1024_t1) rkmWinIterF_w1024_s1a
/-- Cumulative `w1024` part `1` lane witness. -/
theorem rkmHiLane_w1024_wint1 : @rkmWinIterSnd_w1024_s1a = @rkmWinIterSnd_w1024_s1a :=
  (And.intro (Eq.refl rkmHiLane_w1024_wint0) rfl).right

end
end QuantumComputation.Specs.DickeSol
