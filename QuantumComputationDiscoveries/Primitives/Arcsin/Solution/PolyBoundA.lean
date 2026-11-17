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

public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import QuantumComputationDiscoveries.Primitives.Arcsin.Solution.PolyDefs

@[expose] public section

namespace QuantumComputation.Specs

namespace ArcsinImpl

open Function Real Finset


def ckOne : ℕ := 1152921504606846976
def ckH : ℕ := 8796093022208
def ckN : ℕ := 205887
def ckSHL : ℕ := 8796093022122
def ckSHU : ℕ := 8796093022123
def ckCHL : ℕ := 1152921504573292543
def ckCHU : ℕ := 1152921504573292545
def ckPI2L : ℕ := 1811004864519280610
def ckPI2U : ℕ := 1811004864519280811
def ckEPS25 : ℕ := 144115188075
def SCALE37 : ℕ := 137438953472
def SCALE33 : ℕ := 8589934592

structure GS where
  i : ℕ
  sl : ℕ
  su : ℕ
  cl : ℕ
  cu : ℕ
  deriving DecidableEq

def gstep (g : GS) : GS :=
  ⟨Nat.add g.i 1,
   Nat.div (Nat.add (Nat.mul g.sl ckCHL) (Nat.mul g.cl ckSHL)) ckOne,
   Nat.add (Nat.div (Nat.add (Nat.mul g.su ckCHU) (Nat.mul g.cu ckSHU)) ckOne) 1,
   Nat.div (Nat.sub (Nat.mul g.cl ckCHL) (Nat.mul g.su ckSHU)) ckOne,
   Nat.add (Nat.div (Nat.sub (Nat.mul g.cu ckCHU) (Nat.mul g.sl ckSHL)) ckOne) 1⟩

def forceNatGS (v : ℕ) (k : ℕ → GS) : GS :=
  match v with
  | 0 => k 0
  | n + 1 => k (n + 1)

theorem forceNatGS_eq (v : ℕ) (k : ℕ → GS) : forceNatGS v k = k v := by
  cases v <;> rfl

def mkGS (i sl su cl cu : ℕ) : GS :=
  forceNatGS i fun i' =>
  forceNatGS sl fun sl' =>
  forceNatGS su fun su' =>
  forceNatGS cl fun cl' =>
  forceNatGS cu fun cu' =>
  ⟨i', sl', su', cl', cu'⟩

theorem mkGS_eq (i sl su cl cu : ℕ) : mkGS i sl su cl cu = ⟨i, sl, su, cl, cu⟩ := by
  simp only [mkGS, forceNatGS_eq]

def gstepS (g : GS) : GS :=
  mkGS (Nat.add g.i 1)
    (Nat.div (Nat.add (Nat.mul g.sl ckCHL) (Nat.mul g.cl ckSHL)) ckOne)
    (Nat.add (Nat.div (Nat.add (Nat.mul g.su ckCHU) (Nat.mul g.cu ckSHU)) ckOne) 1)
    (Nat.div (Nat.sub (Nat.mul g.cl ckCHL) (Nat.mul g.su ckSHU)) ckOne)
    (Nat.add (Nat.div (Nat.sub (Nat.mul g.cu ckCHU) (Nat.mul g.sl ckSHL)) ckOne) 1)

theorem gstepS_eq (g : GS) : gstepS g = gstep g := by
  unfold gstepS gstep
  rw [mkGS_eq]

def forceGS1 (gn : GS) (k : GS → GS) : GS :=
  match gn with
  | ⟨i, sl, su, cl, cu⟩ => k ⟨i, sl, su, cl, cu⟩

theorem forceGS1_eq (gn : GS) (k : GS → GS) : forceGS1 gn k = k gn := by
  cases gn; rfl

def forceGS2 (gn : GS) (k : GS → GS × GS) : GS × GS :=
  match gn with
  | ⟨i, sl, su, cl, cu⟩ => k ⟨i, sl, su, cl, cu⟩

theorem forceGS2_eq (gn : GS) (k : GS → GS × GS) : forceGS2 gn k = k gn := by
  cases gn; rfl

def g0 : GS := ⟨0, 0, 0, ckOne, ckOne⟩

def advFuel : ℕ := 50

def adv (XP : ℕ) : ℕ → GS → GS → GS × GS
  | 0, g, gn => (g, gn)
  | n + 1, g, gn =>
      cond (and (Nat.blt g.i ckN) (Nat.ble gn.su XP))
        (forceGS2 (gstepS gn) fun gn' => adv XP n gn gn')
        (g, gn)

def stepN : ℕ → GS → GS
  | 0, g => g
  | n + 1, g =>
      cond (Nat.blt g.i ckN)
        (forceGS1 (gstepS g) (stepN n))
        g

def loB (g : GS) (XP : ℕ) : ℕ :=
  cond (Nat.ble g.su XP)
    (min (Nat.add (Nat.mul g.i ckH) (Nat.div (Nat.mul (Nat.sub XP g.su) ckOne) g.cu)) ckPI2L) 0


def loBD_gn (gn : GS) (XP D : ℕ) : ℕ :=
  cond (and (Nat.ble 86 D) (and (Nat.ble D ckH) (and (Nat.ble D (Nat.mul gn.i ckH))
    (Nat.ble (Nat.mul (Nat.sub gn.su XP) ckOne) (Nat.mul gn.cl (Nat.sub D 86))))))
    (min (Nat.sub (Nat.mul gn.i ckH) D) ckPI2L) 0

def loB_gn (g gn : GS) (XP : ℕ) : ℕ :=
  cond (and (Nat.blt g.i ckN) (Nat.ble XP gn.su))
    (loBD_gn gn XP (Nat.add (Nat.div (Nat.mul (Nat.sub gn.su XP) ckOne) gn.cl) 87)) 0

def loB0 (g gn : GS) (XP : ℕ) : ℕ :=
  max (loB g XP) (loB_gn g gn XP)
def hiB (g gn : GS) (XP : ℕ) : ℕ :=
  cond (and (Nat.blt g.i ckN) (Nat.ble XP gn.sl))
    (hiBD gn XP (Nat.div (Nat.mul (Nat.sub gn.sl XP) ckOne) (Nat.add gn.cu (Nat.div gn.su 262144))))
    ckPI2U
where
  hiBD (gn : GS) (XP D : ℕ) : ℕ :=
    cond (and (Nat.ble (Nat.add (Nat.mul (Nat.mul 2 XP) (Nat.mul ckOne ckOne))
        (Nat.add (Nat.mul gn.su (Nat.mul D D)) (Nat.mul (Nat.mul 2 gn.cu) (Nat.mul D ckOne))))
        (Nat.mul (Nat.mul 2 gn.sl) (Nat.mul ckOne ckOne)))
      (Nat.ble D (Nat.mul gn.i ckH)))
      (Nat.sub (Nat.mul gn.i ckH) D) ckPI2U

noncomputable abbrev sc (v : ℕ) : ℝ := (v : ℝ) / (ckOne : ℝ)

theorem ckOne_pos : (0 : ℝ) < ckOne := by norm_num [ckOne]

theorem sc_nonneg (v : ℕ) : 0 ≤ sc v := div_nonneg (Nat.cast_nonneg _) ckOne_pos.le

theorem sc_add (a b : ℕ) : sc (a + b) = sc a + sc b := by
  simp only [sc, Nat.cast_add, add_div]

theorem sc_mul_nat (c a : ℕ) : sc (c * a) = (c : ℝ) * sc a := by
  simp only [sc, Nat.cast_mul, mul_div_assoc]

theorem sc_mono {a b : ℕ} (h : a ≤ b) : sc a ≤ sc b :=
  div_le_div_of_nonneg_right (by exact_mod_cast h) ckOne_pos.le

theorem sc_div_le (a : ℕ) : sc (a / ckOne) ≤ (a : ℝ) / ckOne / ckOne :=
  div_le_div_of_nonneg_right Nat.cast_div_le ckOne_pos.le

theorem le_sc_div_add_one (a : ℕ) : (a : ℝ) / ckOne / ckOne ≤ sc (a / ckOne + 1) := by
  apply div_le_div_of_nonneg_right _ ckOne_pos.le
  have h : a < (a / ckOne + 1) * ckOne := by
    rw [add_mul, one_mul]; exact Nat.lt_div_mul_add (by norm_num [ckOne])
  rw [div_le_iff₀ ckOne_pos]
  exact_mod_cast h.le

theorem sub_le_cast_tsub (a b : ℕ) : (a : ℝ) - b ≤ ((a - b : ℕ) : ℝ) := by
  rcases le_total b a with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero]
    have : (a : ℝ) ≤ b := by exact_mod_cast h
    linarith

theorem sc_mul_H (i : ℕ) : sc (i * ckH) = (i : ℝ) / 131072 := by
  simp only [sc, Nat.cast_mul]; norm_num [ckH, ckOne]; ring

theorem sinh_bounds : sc ckSHL ≤ sin (1 / 131072) ∧ sin (1 / 131072) ≤ sc ckSHU := by
  have h := Real.sin_bound (x := 1 / 131072) (by rw [abs_of_pos (by norm_num)]; norm_num)
  rw [abs_le, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 131072)] at h
  constructor
  · have : sc ckSHL ≤ 1 / 131072 - (1 / 131072) ^ 3 / 6 - (1 / 131072) ^ 5 / 100 := by
      norm_num [sc, ckSHL, ckOne]
    linarith [h.1]
  · have : 1 / 131072 - (1 / 131072) ^ 3 / 6 + (1 / 131072) ^ 5 / 100 ≤ sc ckSHU := by
      norm_num [sc, ckSHU, ckOne]
    linarith [h.2]

theorem cosh_bounds : sc ckCHL ≤ cos (1 / 131072) ∧ cos (1 / 131072) ≤ sc ckCHU := by
  have h := Real.cos_bound (x := 1 / 131072) (by rw [abs_of_pos (by norm_num)]; norm_num)
  rw [abs_le, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 131072)] at h
  constructor
  · have : sc ckCHL ≤ 1 - (1 / 131072) ^ 2 / 2 - (1 / 131072) ^ 4 * (5 / 96) := by
      norm_num [sc, ckCHL, ckOne]
    linarith [h.1]
  · have : 1 - (1 / 131072) ^ 2 / 2 + (1 / 131072) ^ 4 * (5 / 96) ≤ sc ckCHU := by
      norm_num [sc, ckCHU, ckOne]
    linarith [h.2]

theorem sc_PI2L_le : sc ckPI2L ≤ π / 2 := by
  have := pi_gt_d20
  have : sc ckPI2L ≤ 3.14159265358979323846 / 2 := by norm_num [sc, ckPI2L, ckOne]
  linarith

theorem pi_half_le_sc_PI2U : π / 2 ≤ sc ckPI2U := by
  have := pi_lt_d20
  have : 3.14159265358979323847 / 2 ≤ sc ckPI2U := by norm_num [sc, ckPI2U, ckOne]
  linarith

theorem angle_le_pi_half {i : ℕ} (hi : i ≤ ckN) : (i : ℝ) / 131072 ≤ π / 2 := by
  have h1 : (i : ℝ) ≤ 205887 := by exact_mod_cast (hi : i ≤ 205887)
  have := pi_gt_d6
  have : (i : ℝ) / 131072 ≤ 205887 / 131072 := div_le_div_of_nonneg_right h1 (by norm_num)
  linarith

theorem iH_le_PI2L {i : ℕ} (hi : i ≤ ckN) : i * ckH ≤ ckPI2L :=
  (Nat.mul_le_mul_right ckH hi).trans (by norm_num [ckN, ckH, ckPI2L])

structure Sound (g : GS) : Prop where
  hi : g.i ≤ ckN
  sl : sc g.sl ≤ sin ((g.i : ℝ) / 131072)
  su : sin ((g.i : ℝ) / 131072) ≤ sc g.su
  cl : sc g.cl ≤ cos ((g.i : ℝ) / 131072)
  cu : cos ((g.i : ℝ) / 131072) ≤ sc g.cu

theorem sound_g0 : Sound g0 where
  hi := by norm_num [g0, ckN]
  sl := by simp [g0, sc]
  su := by simp [g0, sc]
  cl := by simp [g0, sc, ckOne_pos.ne']
  cu := by simp [g0, sc, ckOne_pos.ne']

theorem Sound.angle_nonneg {g : GS} (_ : Sound g) : (0 : ℝ) ≤ (g.i : ℝ) / 131072 := by positivity

theorem Sound.sin_nonneg {g : GS} (hg : Sound g) : 0 ≤ sin ((g.i : ℝ) / 131072) :=
  sin_nonneg_of_nonneg_of_le_pi hg.angle_nonneg (by linarith [angle_le_pi_half hg.hi, pi_pos])

theorem Sound.cos_nonneg {g : GS} (hg : Sound g) : 0 ≤ cos ((g.i : ℝ) / 131072) :=
  cos_nonneg_of_mem_Icc ⟨by linarith [hg.angle_nonneg, pi_pos], angle_le_pi_half hg.hi⟩

theorem gstep_i (g : GS) : (gstep g).i = g.i + 1 := rfl
theorem gstep_sl (g : GS) : (gstep g).sl = (g.sl * ckCHL + g.cl * ckSHL) / ckOne := rfl
theorem gstep_su (g : GS) : (gstep g).su = (g.su * ckCHU + g.cu * ckSHU) / ckOne + 1 := rfl
theorem gstep_cl (g : GS) : (gstep g).cl = (g.cl * ckCHL - g.su * ckSHU) / ckOne := rfl
theorem gstep_cu (g : GS) : (gstep g).cu = (g.cu * ckCHU - g.sl * ckSHL) / ckOne + 1 := rfl

theorem Sound.step {g : GS} (hg : Sound g) (hlt : g.i < ckN) : Sound (gstep g) := by
  obtain ⟨hsl, hsu⟩ := sinh_bounds
  obtain ⟨hcl, hcu⟩ := cosh_bounds
  have hθ : ((gstep g).i : ℝ) / 131072 = (g.i : ℝ) / 131072 + 1 / 131072 := by
    rw [gstep_i]; push_cast; ring
  have hθ'1 : (g.i : ℝ) / 131072 + 1 / 131072 ≤ π / 2 := by
    have := angle_le_pi_half (i := g.i + 1) hlt
    push_cast at this; linarith
  have hs0 := hg.sin_nonneg
  have hc0 := hg.cos_nonneg
  have hc'0 : 0 ≤ cos ((g.i : ℝ) / 131072 + 1 / 131072) :=
    cos_nonneg_of_mem_Icc ⟨by linarith [hg.angle_nonneg, pi_pos], hθ'1⟩
  have hsh0 : 0 ≤ sc ckSHL := sc_nonneg _
  have hch0 : 0 ≤ sc ckCHL := sc_nonneg _
  have hsh0' : 0 ≤ sin (1 / 131072 : ℝ) := hsh0.trans hsl
  have hch0' : 0 ≤ cos (1 / 131072 : ℝ) := hch0.trans hcl
  have e2 : ∀ a b c d : ℕ,
      ((a * b + c * d : ℕ) : ℝ) / ckOne / ckOne = sc a * sc b + sc c * sc d := by
    intro a b c d; simp only [sc]; push_cast; field_simp
  have e3 : ∀ a b c d : ℕ, ((a * b : ℕ) : ℝ) / ckOne / ckOne - ((c * d : ℕ) : ℝ) / ckOne / ckOne =
      sc a * sc b - sc c * sc d := by
    intro a b c d; simp only [sc]; push_cast; field_simp
  refine ⟨hlt, ?_, ?_, ?_, ?_⟩ <;> rw [hθ]
  · rw [sin_add, gstep_sl]
    calc _ ≤ _ := sc_div_le _
      _ = _ := e2 _ _ _ _
      _ ≤ _ := add_le_add (mul_le_mul hg.sl hcl hch0 hs0) (mul_le_mul hg.cl hsl hsh0 hc0)
  · rw [sin_add, gstep_su]
    refine le_trans ?_ (le_sc_div_add_one _)
    rw [e2]
    exact add_le_add (mul_le_mul hg.su hcu hch0' (sc_nonneg _))
      (mul_le_mul hg.cu hsu hsh0' (sc_nonneg _))
  · rw [gstep_cl]
    refine (sc_div_le _).trans ?_
    rcases le_total (g.su * ckSHU) (g.cl * ckCHL) with h | h
    · rw [Nat.cast_sub h, sub_div, sub_div, e3, cos_add]
      exact sub_le_sub (mul_le_mul hg.cl hcl hch0 hc0) (mul_le_mul hg.su hsu hsh0' (sc_nonneg _))
    · rw [Nat.sub_eq_zero_of_le h]; simpa using hc'0
  · rw [cos_add, gstep_cu]
    refine le_trans ?_ (le_sc_div_add_one _)
    refine le_trans ?_ (div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right (sub_le_cast_tsub _ _) ckOne_pos.le) ckOne_pos.le)
    rw [sub_div, sub_div, e3]
    exact sub_le_sub (mul_le_mul hg.cu hcu hch0' (sc_nonneg _)) (mul_le_mul hg.sl hsl hsh0 hs0)

def Inv (g gn : GS) : Prop := Sound g ∧ gn = gstep g

theorem inv_g0 : Inv g0 (gstep g0) := ⟨sound_g0, rfl⟩

theorem inv_gstepS {g : GS} (h : Inv g (gstep g)) : Inv g (gstepS g) :=
  (gstepS_eq g).symm ▸ h

theorem stepN_inv : ∀ (n : ℕ) (g : GS), Inv g (gstep g) →
    Inv (stepN n g) (gstep (stepN n g))
  | 0, _, h => h
  | n + 1, g, h => by
      change Inv (cond (Nat.blt g.i ckN) (forceGS1 (gstepS g) (stepN n)) g)
               (gstep (cond (Nat.blt g.i ckN) (forceGS1 (gstepS g) (stepN n)) g))
      cases hlt : Nat.blt g.i ckN
      · exact h
      · rw [Bool.cond_true, forceGS1_eq, gstepS_eq]
        exact stepN_inv n (gstep g) ⟨h.1.step (Nat.blt_eq.mp hlt), rfl⟩

theorem adv_inv (XP : ℕ) : ∀ n g gn, Inv g gn → Inv (adv XP n g gn).1 (adv XP n g gn).2
  | 0, _, _, h => h
  | n + 1, g, gn, h => by
    change Inv (cond _ (forceGS2 (gstepS gn) fun gn' => adv XP n gn gn') (g, gn)).1
             (cond _ (forceGS2 (gstepS gn) fun gn' => adv XP n gn gn') (g, gn)).2
    cases hc : (and (Nat.blt g.i ckN) (Nat.ble gn.su XP))
    · exact h
    · rw [Bool.cond_true, forceGS2_eq, gstepS_eq]
      apply adv_inv XP n
      have hlt : g.i < ckN := by
        simp only [Bool.and_eq_true, Nat.blt_eq] at hc; exact hc.1
      exact ⟨h.2 ▸ h.1.step hlt, rfl⟩

theorem loB_eq (g : GS) (XP : ℕ) : loB g XP =
    cond (Nat.ble g.su XP) (min (g.i * ckH + (XP - g.su) * ckOne / g.cu) ckPI2L) 0 := rfl
theorem hiB_eq (g gn : GS) (XP : ℕ) : hiB g gn XP =
    cond (and (Nat.blt g.i ckN) (Nat.ble XP gn.sl))
      (hiB.hiBD gn XP ((gn.sl - XP) * ckOne / (gn.cu + gn.su / 262144))) ckPI2U := rfl
theorem hiBD_eq (gn : GS) (XP D : ℕ) : hiB.hiBD gn XP D =
    cond (and (Nat.ble (2 * XP * (ckOne * ckOne) + (gn.su * (D * D) + 2 * gn.cu * (D * ckOne)))
        (2 * gn.sl * (ckOne * ckOne))) (Nat.ble D (gn.i * ckH))) (gn.i * ckH - D) ckPI2U := rfl


theorem loBD_gn_eq (gn : GS) (XP D : ℕ) : loBD_gn gn XP D =
    cond (and (Nat.ble 86 D) (and (Nat.ble D ckH) (and (Nat.ble D (gn.i * ckH))
      (Nat.ble ((gn.su - XP) * ckOne) (gn.cl * (D - 86))))))
      (min (gn.i * ckH - D) ckPI2L) 0 := rfl
theorem loB_gn_eq (g gn : GS) (XP : ℕ) : loB_gn g gn XP =
    cond (and (Nat.blt g.i ckN) (Nat.ble XP gn.su))
      (loBD_gn gn XP ((gn.su - XP) * ckOne / gn.cl + 87)) 0 := rfl

theorem sc_sub_86_le_sin {D : ℕ} (hD1 : 86 ≤ D) (hDH : D ≤ ckH) :
    sc (D - 86) ≤ sin (sc D) := by
  have hd0 : 0 ≤ sc D := sc_nonneg D
  have hdH : sc D ≤ 1 / 131072 := by
    have := sc_mono hDH
    have hH : sc ckH = 1 / 131072 := by norm_num [sc, ckH, ckOne]
    linarith
  have h := Real.sin_bound (x := sc D) (by rw [abs_of_nonneg hd0]; linarith)
  rw [abs_le, abs_of_nonneg hd0] at h
  have hpow3 : (sc D) ^ 3 ≤ (1 / 131072 : ℝ) ^ 3 := pow_le_pow_left₀ hd0 hdH 3
  have hpow5 : (sc D) ^ 5 ≤ (1 / 131072 : ℝ) ^ 5 := pow_le_pow_left₀ hd0 hdH 5
  have h3 : (sc D) ^ 3 / 6 ≤ (1 / 131072 : ℝ) ^ 3 / 6 :=
    div_le_div_of_nonneg_right hpow3 (by norm_num)
  have h5 : (sc D) ^ 5 / 100 ≤ (1 / 131072 : ℝ) ^ 5 / 100 :=
    div_le_div_of_nonneg_right hpow5 (by norm_num)
  have hsub : sc (D - 86) = sc D - 86 / 1152921504606846976 := by
    simp only [sc, ckOne, Nat.cast_sub hD1]; push_cast; ring
  have hnum : (1 / 131072 : ℝ) ^ 3 / 6 + (1 / 131072 : ℝ) ^ 5 / 100 ≤ 86 / 1152921504606846976 := by
    norm_num
  linarith [h.1]

theorem loBD_gn_sound {gn : GS} (hgn : Sound gn) {XP : ℕ} (hsu : XP ≤ gn.su) (D : ℕ) :
    sc (loBD_gn gn XP D) ≤ arcsin (sc XP) := by
  rw [loBD_gn_eq]
  cases hc : (and (Nat.ble 86 D) (and (Nat.ble D ckH) (and (Nat.ble D (gn.i * ckH))
    (Nat.ble ((gn.su - XP) * ckOne) (gn.cl * (D - 86))))))
  · rw [Bool.cond_false]; simp only [sc, Nat.cast_zero, zero_div]
    exact arcsin_nonneg.mpr (sc_nonneg XP)
  rw [Bool.cond_true]
  simp only [Bool.and_eq_true, Nat.ble_eq] at hc
  obtain ⟨hD1, hDH, hDi, hchk⟩ := hc
  set v := min (gn.i * ckH - D) ckPI2L
  have hv1 : v ≤ gn.i * ckH - D := min_le_left _ _
  have hv2 : v ≤ ckPI2L := min_le_right _ _
  have hφ_hi : sc v ≤ π / 2 := (sc_mono hv2).trans sc_PI2L_le
  have hφ_lo : -(π / 2) ≤ sc v := by linarith [sc_nonneg v, pi_pos]
  have hφ_le : sc v ≤ (gn.i : ℝ) / 131072 - sc D := by
    calc sc v ≤ sc (gn.i * ckH - D) := sc_mono hv1
      _ = sc (gn.i * ckH) - sc D := by simp only [sc, Nat.cast_sub hDi, sub_div]
      _ = (gn.i : ℝ) / 131072 - sc D := by rw [sc_mul_H]
  have hθ_hi : (gn.i : ℝ) / 131072 ≤ π / 2 := angle_le_pi_half hgn.hi
  have hθ_sub_hi : (gn.i : ℝ) / 131072 - sc D ≤ π / 2 := by linarith [sc_nonneg D]
  have hsin_mono : sin (sc v) ≤ sin ((gn.i : ℝ) / 131072 - sc D) :=
    sin_le_sin_of_le_of_le_pi_div_two hφ_lo hθ_sub_hi hφ_le
  have hkey : sc gn.su - sc XP ≤ sc gn.cl * sc (D - 86) := by
    have hr : (((gn.su - XP : ℕ) * ckOne : ℕ) : ℝ) ≤ (gn.cl * (D - 86) : ℕ) := by
      exact_mod_cast hchk
    push_cast at hr
    rw [Nat.cast_sub hsu] at hr
    have hO := ckOne_pos
    simp only [sc]
    rw [div_mul_div_comm, ← sub_div, div_le_div_iff₀ hO (mul_pos hO hO)]
    nlinarith
  have hd_sin := sc_sub_86_le_sin hD1 hDH
  have hsinD_nonneg : 0 ≤ sin (sc D) := (sc_nonneg (D - 86)).trans hd_sin
  have hsin : sin ((gn.i : ℝ) / 131072 - sc D) ≤ sc XP := by
    rw [sin_sub]
    have t1 : sin ((gn.i : ℝ) / 131072) * cos (sc D) ≤ sc gn.su := by
      calc sin ((gn.i : ℝ) / 131072) * cos (sc D)
          ≤ sin ((gn.i : ℝ) / 131072) * 1 := mul_le_mul_of_nonneg_left (cos_le_one _) hgn.sin_nonneg
        _ ≤ sc gn.su := by linarith [hgn.su]
    have t2 : sc gn.cl * sc (D - 86) ≤ cos ((gn.i : ℝ) / 131072) * sin (sc D) := by
      calc sc gn.cl * sc (D - 86)
          ≤ sc gn.cl * sin (sc D) := mul_le_mul_of_nonneg_left hd_sin (sc_nonneg _)
        _ ≤ cos ((gn.i : ℝ) / 131072) * sin (sc D) := mul_le_mul_of_nonneg_right hgn.cl hsinD_nonneg
    linarith
  calc sc v = arcsin (sin (sc v)) := (arcsin_sin hφ_lo hφ_hi).symm
    _ ≤ arcsin (sc XP) := arcsin_le_arcsin (hsin_mono.trans hsin)

theorem loB_gn_sound {g gn : GS} (h : Inv g gn) (XP : ℕ) :
    sc (loB_gn g gn XP) ≤ arcsin (sc XP) := by
  rw [loB_gn_eq]
  cases hc : (and (Nat.blt g.i ckN) (Nat.ble XP gn.su))
  · rw [Bool.cond_false]; simp only [sc, Nat.cast_zero, zero_div]
    exact arcsin_nonneg.mpr (sc_nonneg XP)
  rw [Bool.cond_true]
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hc
  exact loBD_gn_sound (h.2 ▸ h.1.step hc.1) hc.2 _
theorem loB_affine_props {g : GS} (hg : Sound g) {XP : ℕ} (hsu : g.su ≤ XP) :
    (g.i : ℝ) / 131072 ≤ sc (loB g XP) ∧
    sc (loB g XP) ≤ π / 2 ∧
    sc g.cu * (sc (loB g XP) - (g.i : ℝ) / 131072) ≤ sc XP - sc g.su := by
  rw [loB_eq, Nat.ble_eq.mpr hsu, Bool.cond_true]
  obtain ⟨D, hD⟩ : ∃ D, (XP - g.su) * ckOne / g.cu = D := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, min (g.i * ckH + D) ckPI2L = v := ⟨_, rfl⟩
  rw [hD, hv]
  have hv1 : g.i * ckH ≤ v := hv ▸ le_min (Nat.le_add_right _ _) (iH_le_PI2L hg.hi)
  have hv2 : v ≤ g.i * ckH + D := hv ▸ min_le_left _ _
  have hv3 : v ≤ ckPI2L := hv ▸ min_le_right _ _
  have hd0 : (g.i : ℝ) / 131072 ≤ sc v := by have := sc_mono hv1; rwa [sc_mul_H] at this
  have hdD : sc v ≤ (g.i : ℝ) / 131072 + sc D := by
    have := sc_mono hv2; rwa [sc_add, sc_mul_H] at this
  have hφ1 : sc v ≤ π / 2 := (sc_mono hv3).trans sc_PI2L_le
  have hO := ckOne_pos
  have hcuD : sc g.cu * sc D ≤ sc XP - sc g.su := by
    have h1 : D * g.cu ≤ (XP - g.su) * ckOne := hD ▸ Nat.div_mul_le_self _ _
    have h2 : (D : ℝ) * g.cu ≤ ((XP - g.su : ℕ) : ℝ) * ckOne := by exact_mod_cast h1
    rw [Nat.cast_sub hsu] at h2
    simp only [sc]
    rw [div_mul_div_comm, div_le_iff₀ (mul_pos hO hO)]
    have : ((XP : ℝ) / ckOne - g.su / ckOne) * (ckOne * ckOne) = ((XP : ℝ) - g.su) * ckOne := by
      field_simp
    rw [this]; linarith
  refine ⟨hd0, hφ1, ?_⟩
  calc sc g.cu * (sc v - (g.i : ℝ) / 131072)
      ≤ sc g.cu * sc D := mul_le_mul_of_nonneg_left (by linarith) (sc_nonneg _)
    _ ≤ sc XP - sc g.su := hcuD

theorem loB_secant_sound {g : GS} (hg : Sound g) {XA XB : ℕ}
    (hsuA : g.su ≤ XA) (hsuB : g.su ≤ XB)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * sc (loB g XA) + b * sc (loB g XB) ≤ arcsin (a * sc XA + b * sc XB) := by
  obtain ⟨hdA, hφA, hcuA⟩ := loB_affine_props hg hsuA
  obtain ⟨hdB, hφB, hcuB⟩ := loB_affine_props hg hsuB
  set v := a * sc (loB g XA) + b * sc (loB g XB)
  set X := a * sc XA + b * sc XB
  have hdv : (g.i : ℝ) / 131072 ≤ v := by
    have : a * ((g.i : ℝ) / 131072) + b * ((g.i : ℝ) / 131072) = (g.i : ℝ) / 131072 := by
      linear_combination ((g.i : ℝ) / 131072) * hab
    nlinarith
  have hφv : v ≤ π / 2 := by
    have : a * (π / 2) + b * (π / 2) = π / 2 := by linear_combination (π / 2) * hab
    nlinarith
  have hφ_lo : -(π / 2) ≤ v := by linarith [hg.angle_nonneg, pi_pos]
  have hcuv : sc g.cu * (v - (g.i : ℝ) / 131072) ≤ X - sc g.su := by
    have h1 := mul_le_mul_of_nonneg_left hcuA ha
    have h2 := mul_le_mul_of_nonneg_left hcuB hb
    have heq1 : a * (sc g.cu * (sc (loB g XA) - (g.i : ℝ) / 131072)) +
                b * (sc g.cu * (sc (loB g XB) - (g.i : ℝ) / 131072)) =
                sc g.cu * (v - (g.i : ℝ) / 131072) := by
      dsimp only [v]; linear_combination -sc g.cu * ((g.i : ℝ) / 131072) * hab
    have heq2 : a * (sc XA - sc g.su) + b * (sc XB - sc g.su) = X - sc g.su := by
      dsimp only [X]; linear_combination -sc g.su * hab
    linarith
  have hsin : sin v ≤ X := by
    have e : v = (g.i : ℝ) / 131072 + (v - (g.i : ℝ) / 131072) := by ring
    rw [e, sin_add]
    have hd0' : 0 ≤ v - (g.i : ℝ) / 131072 := by linarith
    have t1 := mul_le_of_le_one_right hg.sin_nonneg (cos_le_one (v - (g.i : ℝ) / 131072))
    have t2 := mul_le_mul_of_nonneg_left (sin_le hd0') hg.cos_nonneg
    have t3 :
        cos ((g.i : ℝ) / 131072) * (v - (g.i : ℝ) / 131072) ≤ sc g.cu * (v - (g.i : ℝ) / 131072) :=
      mul_le_mul hg.cu le_rfl hd0' (sc_nonneg _)
    linarith [hg.su]
  calc v = arcsin (sin v) := (arcsin_sin hφ_lo hφv).symm
    _ ≤ arcsin X := arcsin_le_arcsin hsin

theorem loB_sound_pt {g : GS} (hg : Sound g) (XP : ℕ) : sc (loB g XP) ≤ arcsin (sc XP) := by
  cases hsu : Nat.ble g.su XP
  · rw [loB_eq, hsu, Bool.cond_false]
    simp only [sc, Nat.cast_zero, zero_div]
    exact arcsin_nonneg.mpr (sc_nonneg XP)
  · have hsu' : g.su ≤ XP := Nat.ble_eq.mp hsu
    have h := loB_secant_sound hg hsu' hsu' (a := 1) (b := 0) (by norm_num) (by norm_num) (by ring)
    simpa using h

theorem hiBD_sound {gn : GS} (hgn : Sound gn) (XP D : ℕ) :
    arcsin (sc XP) ≤ sc (hiB.hiBD gn XP D) := by
  have hfb : arcsin (sc XP) ≤ sc ckPI2U := (arcsin_le_pi_div_two _).trans pi_half_le_sc_PI2U
  rw [hiBD_eq]
  cases hc2 : (and (Nat.ble (2 * XP * (ckOne * ckOne) + (gn.su * (D * D) + 2 * gn.cu * (D * ckOne)))
        (2 * gn.sl * (ckOne * ckOne))) (Nat.ble D (gn.i * ckH)))
  · rw [Bool.cond_false]; exact hfb
  rw [Bool.cond_true]
  simp only [Bool.and_eq_true, Nat.ble_eq] at hc2
  obtain ⟨hchk, hD⟩ := hc2
  have hd0 : 0 ≤ sc D := sc_nonneg D
  have hφ : sc (gn.i * ckH - D) = (gn.i : ℝ) / 131072 - sc D := by
    rw [← sc_mul_H]; simp only [sc]; rw [Nat.cast_sub hD, sub_div]
  have hθ1 : (gn.i : ℝ) / 131072 ≤ π / 2 := angle_le_pi_half hgn.hi
  have hφ0 : 0 ≤ (gn.i : ℝ) / 131072 - sc D := by rw [← hφ]; exact sc_nonneg _
  have hs0 := hgn.sin_nonneg
  have hc0 := hgn.cos_nonneg
  have key : sc XP + sc gn.su * sc D ^ 2 / 2 + sc gn.cu * sc D ≤ sc gn.sl := by
    have hr : (2 * XP * (ckOne * ckOne) + (gn.su * (D * D) + 2 * gn.cu * (D * ckOne)) : ℝ) ≤
        2 * gn.sl * (ckOne * ckOne) := by exact_mod_cast hchk
    have e : sc gn.sl - (sc XP + sc gn.su * sc D ^ 2 / 2 + sc gn.cu * sc D) =
        (2 * gn.sl * (ckOne * ckOne) - (2 * XP * (ckOne * ckOne) +
          (gn.su * (D * D) + 2 * gn.cu * (D * ckOne)))) / (2 * (ckOne : ℝ) ^ 3) := by
      simp only [sc]; field_simp; ring
    have : 0 ≤ sc gn.sl - (sc XP + sc gn.su * sc D ^ 2 / 2 + sc gn.cu * sc D) := by
      rw [e]; exact div_nonneg (by linarith) (by positivity)
    linarith
  have hsin : sc XP ≤ sin ((gn.i : ℝ) / 131072 - sc D) := by
    rw [sin_sub]
    have t1 := mul_le_mul_of_nonneg_left (one_sub_sq_div_two_le_cos (x := sc D)) hs0
    have t2 : sin ((gn.i : ℝ) / 131072) * (sc D ^ 2 / 2) ≤ sc gn.su * (sc D ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right hgn.su (by positivity)
    have t3 := mul_le_mul_of_nonneg_left (sin_le hd0) hc0
    have t4 : cos ((gn.i : ℝ) / 131072) * sc D ≤ sc gn.cu * sc D :=
      mul_le_mul_of_nonneg_right hgn.cu hd0
    nlinarith [hgn.sl]
  rw [hφ]
  calc arcsin (sc XP) ≤ arcsin (sin ((gn.i : ℝ) / 131072 - sc D)) := arcsin_le_arcsin hsin
    _ = _ := arcsin_sin (by linarith [pi_pos]) (by linarith)

theorem hiB_sound {g gn : GS} (h : Inv g gn) (XP : ℕ) : arcsin (sc XP) ≤ sc (hiB g gn XP) := by
  have hfb : arcsin (sc XP) ≤ sc ckPI2U := (arcsin_le_pi_div_two _).trans pi_half_le_sc_PI2U
  rw [hiB_eq]
  cases hc : (and (Nat.blt g.i ckN) (Nat.ble XP gn.sl))
  · rw [Bool.cond_false]; exact hfb
  rw [Bool.cond_true]
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hc
  exact hiBD_sound (h.2 ▸ h.1.step hc.1) XP _

theorem arcsin_secant_sound {xA xB : ℝ} (hxA0 : 0 ≤ xA) (hxA1 : xA ≤ 1)
    (hxB0 : 0 ≤ xB) (hxB1 : xB ≤ 1)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    arcsin (a * xA + b * xB) ≤ a * arcsin xA + b * arcsin xB := by
  set θA := arcsin xA
  set θB := arcsin xB
  have hθA0 : 0 ≤ θA := arcsin_nonneg.2 hxA0
  have hθB0 : 0 ≤ θB := arcsin_nonneg.2 hxB0
  have hθA1 : θA ≤ π / 2 := arcsin_le_pi_div_two xA
  have hθB1 : θB ≤ π / 2 := arcsin_le_pi_div_two xB
  have hmemA : θA ∈ Set.Icc 0 π := ⟨hθA0, by linarith [pi_pos]⟩
  have hmemB : θB ∈ Set.Icc 0 π := ⟨hθB0, by linarith [pi_pos]⟩
  have hconc := strictConcaveOn_sin_Icc.concaveOn.2 hmemA hmemB ha hb hab
  simp only [smul_eq_mul] at hconc
  rw [sin_arcsin (by linarith) hxA1, sin_arcsin (by linarith) hxB1] at hconc
  have hθ_lo : -(π / 2) ≤ a * θA + b * θB := by nlinarith [pi_pos]
  have hθ_hi : a * θA + b * θB ≤ π / 2 := by
    have : a * (π / 2) + b * (π / 2) = π / 2 := by linear_combination (π / 2) * hab
    nlinarith
  calc arcsin (a * xA + b * xB)
      ≤ arcsin (sin (a * θA + b * θB)) := arcsin_le_arcsin hconc
    _ = a * θA + b * θB := arcsin_sin hθ_lo hθ_hi

theorem sc_ckEPS25 : sc ckEPS25 ≤ 1.25e-7 := by
  norm_num [sc, ckEPS25, ckOne]

theorem sc_mul37 (a : ℕ) : sc (a * SCALE37) = (a : ℝ) / 2 ^ 23 := by
  simp only [sc, Nat.cast_mul, ckOne, SCALE37]; push_cast; ring

theorem loB0_sound_pt {g gn : GS} (h : Inv g gn) (XP : ℕ) : sc (loB0 g gn XP) ≤ arcsin (sc XP) := by
  unfold loB0
  rcases le_total (loB g XP) (loB_gn g gn XP) with hle | hle
  · rw [max_eq_right hle]; exact loB_gn_sound h XP
  · rw [max_eq_left hle]; exact loB_sound_pt h.1 XP

theorem sc_mul33 (a : ℕ) : sc (a * SCALE33) = (a : ℝ) / 2 ^ 27 := by
  simp only [sc, Nat.cast_mul, ckOne, SCALE33]; push_cast; ring

-- ============================================================================
-- Bit-Additivity, Bit-Linear Slope Decomposition, and Envelope Bounds
-- ============================================================================

theorem shiftLeft_eq_mul_pow : ∀ (a n : ℕ), Nat.shiftLeft a n = a * 2 ^ n
  | _, 0 => by simp [Nat.shiftLeft]
  | a, n + 1 => by
    change Nat.shiftLeft (2 * a) n = a * 2 ^ (n + 1)
    rw [shiftLeft_eq_mul_pow (2 * a) n]
    ring

theorem add_div_eq_of_dvd {u blk p i : ℕ} (hu : u % blk = 0) (hi : i < blk)
    (hp : p % blk = 0) : (u + i) / p = u / p := by
  have hblk : 0 < blk := by omega
  obtain ⟨q, rfl⟩ := Nat.dvd_of_mod_eq_zero hu
  obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero hp
  rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
      Nat.mul_add_div hblk, Nat.div_eq_of_lt hi, add_zero, Nat.mul_div_cancel_left q hblk]

theorem testBit_add_of_lt {u b i idx : ℕ} (hu : u % 2 ^ b = 0) (hi : i < 2 ^ b) (hidx : idx < b) :
    (u + i).testBit idx = i.testBit idx ∧ u.testBit idx = false := by
  have hmod1 : (u + i) % 2 ^ b = i := by
    rw [Nat.add_mod, hu, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hi]
  have htb1 := Nat.testBit_mod_two_pow (u + i) b idx
  rw [hmod1, decide_eq_true hidx, Bool.true_and] at htb1
  have htb2 := Nat.testBit_mod_two_pow u b idx
  rw [hu, Nat.zero_testBit, decide_eq_true hidx, Bool.true_and] at htb2
  exact ⟨htb1.symm, htb2.symm⟩

theorem testBit_add_of_ge {u b i idx : ℕ} (hu : u % 2 ^ b = 0) (hi : i < 2 ^ b) (hidx : b ≤ idx) :
    (u + i).testBit idx = u.testBit idx ∧ i.testBit idx = false := by
  have hi_false : i.testBit idx = false :=
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by omega) hidx))
  have hdiv : (u + i) / 2 ^ b = u / 2 ^ b := add_div_eq_of_dvd hu hi (Nat.mod_self _)
  have htb : (u + i).testBit idx = u.testBit idx := by
    rw [show idx = (idx - b) + b by omega, Nat.testBit_add, Nat.testBit_add, hdiv]
  exact ⟨htb, hi_false⟩


theorem cond_uRotBit_add {u b i s4 : ℕ} (hu : u % 2 ^ b = 0) (hi : i < 2 ^ b) (j : ℕ) :
    cond (uRotBit (u + i) s4 j) 1 0 =
      cond (uRotBit u s4 j) 1 0 + cond (uRotBit i s4 j) 1 0 := by
  unfold uRotBit
  set src := uRotSrc s4 j
  by_cases hsrc : src < b
  · obtain ⟨h1, h2⟩ := testBit_add_of_lt hu hi hsrc
    rw [h1, h2]; cases i.testBit src <;> rfl
  · obtain ⟨h1, h2⟩ := testBit_add_of_ge hu hi (Nat.le_of_not_lt hsrc)
    rw [h1, h2]; cases u.testBit src <;> rfl

theorem evalBits_uRotBit_add {u b i s4 : ℕ} (hu : u % 2 ^ b = 0) (hi : i < 2 ^ b)
    (start : ℕ) :
    ∀ len, evalBits (uRotBit (u + i) s4) start len =
      evalBits (uRotBit u s4) start len + evalBits (uRotBit i s4) start len
  | 0 => rfl
  | len + 1 => by
    simp only [evalBits, cond_uRotBit_add hu hi, shiftLeft_eq_mul_pow,
      evalBits_uRotBit_add hu hi start len]
    ring

theorem slopeTermPos27_add {u b i s4 : ℕ} (hu : u % 2 ^ b = 0) (hi : i < 2 ^ b)
    (kv bit_idx b_min len mul_pow : ℕ) :
    slopeTermPos27 kv bit_idx b_min len mul_pow s4 (u + i) =
      slopeTermPos27 kv bit_idx b_min len mul_pow s4 u +
      slopeTermPos27 kv bit_idx b_min len mul_pow s4 i := by
  unfold slopeTermPos27
  cases kv.testBit bit_idx
  · rfl
  · simp only [Bool.cond_true, evalBits_uRotBit_add hu hi]
    ring

theorem slopeTermNeg27_add {u b i s4 : ℕ} (hu : u % 2 ^ b = 0) (hi : i < 2 ^ b)
    (kv bit_idx b_min len mul_pow : ℕ) :
    slopeTermNeg27 kv bit_idx b_min len mul_pow s4 (u + i) =
      slopeTermNeg27 kv bit_idx b_min len mul_pow s4 u +
      slopeTermNeg27 kv bit_idx b_min len mul_pow s4 i := by
  unfold slopeTermNeg27
  cases kv.testBit bit_idx
  · simp only [Bool.not_false, Bool.cond_true, evalBits_uRotBit_add hu hi]
    ring
  · rfl

theorem posSlope27_add {u b i s4 : ℕ} (hu : u % 2 ^ b = 0) (hi : i < 2 ^ b) (kv : ℕ) :
    posSlope27 kv s4 (u + i) = posSlope27 kv s4 u + posSlope27 kv s4 i := by
  unfold posSlope27
  simp only [evalBits_uRotBit_add hu hi, slopeTermPos27_add hu hi]
  ring

theorem negSlope27_add {u b i s4 : ℕ} (hu : u % 2 ^ b = 0) (hi : i < 2 ^ b) (kv : ℕ) :
    negSlope27 kv s4 (u + i) = negSlope27 kv s4 u + negSlope27 kv s4 i := by
  unfold negSlope27
  simp only [slopeTermNeg27_add hu hi]
  ring

theorem posSlope27_zero (s4 kv : ℕ) : posSlope27 kv s4 0 = 0 := by
  have h := posSlope27_add (u := 0) (b := 0) (i := 0) (s4 := s4) rfl (by omega) kv
  rw [Nat.zero_add] at h
  omega

theorem negSlope27_zero (s4 kv : ℕ) : negSlope27 kv s4 0 = 0 := by
  have h := negSlope27_add (u := 0) (b := 0) (i := 0) (s4 := s4) rfl (by omega) kv
  rw [Nat.zero_add] at h
  omega

def wBit27 (kv s4 r : ℕ) : ℕ :=
  (16 * 2 ^ r + posSlope27 kv s4 (2 ^ r)) - negSlope27 kv s4 (2 ^ r)

def wBitOK27 (kv s4 : ℕ) : ℕ → Bool
  | 0 => true
  | r + 1 =>
      wBitOK27 kv s4 r &&
      Nat.ble (negSlope27 kv s4 (2 ^ r)) (16 * 2 ^ r + posSlope27 kv s4 (2 ^ r))

def bitLin27 (kv s4 i : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 => bitLin27 kv s4 i r + cond (i.testBit r) (wBit27 kv s4 r) 0

theorem mod_pow_succ_eq_add_cond (i r : ℕ) :
    i % 2 ^ (r + 1) = cond (i.testBit r) (2 ^ r) 0 + i % 2 ^ r := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  cases h : decide (i / 2 ^ r % 2 = 1)
  · simp only [decide_eq_false_iff_not] at h
    have : i / 2 ^ r % 2 = 0 := by omega
    simp [this]
  · simp only [decide_eq_true_eq] at h
    simp [h]; omega

theorem bitLin27_mod_eq (s4 kv i : ℕ) :
    ∀ r, wBitOK27 kv s4 r = true →
      negSlope27 kv s4 (i % 2 ^ r) ≤ 16 * (i % 2 ^ r) + posSlope27 kv s4 (i % 2 ^ r) ∧
      (16 * (i % 2 ^ r) + posSlope27 kv s4 (i % 2 ^ r)) - negSlope27 kv s4 (i % 2 ^ r) =
        bitLin27 kv s4 i r
  | 0, _ => by
    simp [Nat.mod_one, posSlope27_zero, negSlope27_zero, bitLin27]
  | r + 1, hok => by
    dsimp only [wBitOK27] at hok
    simp only [Bool.and_eq_true, Nat.ble_eq] at hok
    obtain ⟨hok_r, hle_r⟩ := hok
    obtain ⟨ih1, ih2⟩ := bitLin27_mod_eq s4 kv i r hok_r
    have hmod_lt : i % 2 ^ r < 2 ^ r := Nat.mod_lt _ (by positivity)
    have hdiv_r : (cond (i.testBit r) (2 ^ r) 0) % 2 ^ r = 0 := by
      cases i.testBit r <;> simp
    have hp := posSlope27_add (s4 := s4) hdiv_r hmod_lt kv
    have hn := negSlope27_add (s4 := s4) hdiv_r hmod_lt kv
    rw [← mod_pow_succ_eq_add_cond] at hp hn
    rw [hp, hn, mod_pow_succ_eq_add_cond, bitLin27]
    cases i.testBit r
    · simp only [cond, zero_add, posSlope27_zero, negSlope27_zero, add_zero]
      exact ⟨ih1, ih2⟩
    · simp only [cond, wBit27]
      omega

theorem bitLin27_eq {kv s4 b_sub i : ℕ} (hok : wBitOK27 kv s4 b_sub = true)
    (hi : i < 2 ^ b_sub) :
    negSlope27 kv s4 i ≤ 16 * i + posSlope27 kv s4 i ∧
    (16 * i + posSlope27 kv s4 i) - negSlope27 kv s4 i = bitLin27 kv s4 i b_sub := by
  have h := bitLin27_mod_eq s4 kv i b_sub hok
  rwa [Nat.mod_eq_of_lt hi] at h

def curvBitGe25 (s4 b_sub j : ℕ) : Bool :=
  Nat.ble b_sub (uRotSrc s4 j)

def curvConstOK25 (s4 b_sub : ℕ) : Bool :=
  Nat.beq b_sub 0 ||
  (curvBitGe25 s4 b_sub 6 && curvBitGe25 s4 b_sub 7 && curvBitGe25 s4 b_sub 8 &&
   curvBitGe25 s4 b_sub 9 && curvBitGe25 s4 b_sub 10 && curvBitGe25 s4 b_sub 11 &&
   curvBitGe25 s4 b_sub 12 && curvBitGe25 s4 b_sub 13 && curvBitGe25 s4 b_sub 14 &&
   curvBitGe25 s4 b_sub 15)

theorem uRotBit_add_of_ge {u b_sub i s4 j : ℕ}
    (hu : u % 2 ^ b_sub = 0) (hi : i < 2 ^ b_sub)
    (hge : curvBitGe25 s4 b_sub j = true) :
    uRotBit (u + i) s4 j = uRotBit u s4 j := by
  unfold curvBitGe25 at hge
  unfold uRotBit
  exact (testBit_add_of_ge hu hi (Nat.ble_eq.mp hge)).1

theorem d9Val_add_eq {s4 b_sub u i : ℕ}
    (hc : curvConstOK25 s4 b_sub = true)
    (hu : u % 2 ^ b_sub = 0) (hi : i < 2 ^ b_sub) :
    d9Val (u + i) s4 = d9Val u s4 := by
  unfold curvConstOK25 at hc
  rcases Bool.or_eq_true_iff.mp hc with hb0 | hall
  · rw [Nat.beq_eq.mp hb0] at hi
    have hi0 : i = 0 := by omega
    subst hi0; simp
  · simp only [Bool.and_eq_true] at hall
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨j6, j7⟩, j8⟩, j9⟩, j10⟩, j11⟩, j12⟩, j13⟩, j14⟩, j15⟩ := hall
    unfold d9Val
    simp [evalBits, uRotBit_add_of_ge hu hi j6, uRotBit_add_of_ge hu hi j7,
      uRotBit_add_of_ge hu hi j8, uRotBit_add_of_ge hu hi j9,
      uRotBit_add_of_ge hu hi j10, uRotBit_add_of_ge hu hi j11,
      uRotBit_add_of_ge hu hi j12, uRotBit_add_of_ge hu hi j13,
      uRotBit_add_of_ge hu hi j14, uRotBit_add_of_ge hu hi j15]

theorem diff27_add_eq {b_base kv lv s4 b_sub u i : ℕ}
    (hw : wBitOK27 kv s4 b_sub = true)
    (hc : curvConstOK25 s4 b_sub = true)
    (hu : u % 2 ^ b_sub = 0) (hi : i < 2 ^ b_sub)
    (hzle : zNeg27 kv s4 u ≤ zPos27 b_base kv lv s4 u) :
    zNeg27 kv s4 (u + i) ≤ zPos27 b_base kv lv s4 (u + i) ∧
    diff27 b_base kv lv s4 (u + i) =
      diff27 b_base kv lv s4 u + bitLin27 kv s4 i b_sub := by
  obtain ⟨hbit_le, hbit_eq⟩ := bitLin27_eq hw hi
  have hd9 := d9Val_add_eq hc hu hi
  have hp := posSlope27_add (s4 := s4) hu hi kv
  have hn := negSlope27_add (s4 := s4) hu hi kv
  unfold diff27 zPos27 zNeg27 at *
  rw [hp, hn, hd9]
  omega

def dMaxSum27 (kv s4 blk gNum : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 => dMaxSum27 kv s4 blk gNum r + (blk * wBit27 kv s4 r - gNum * 2 ^ r)

def dMinAbsSum27 (kv s4 blk gNum : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 => dMinAbsSum27 kv s4 blk gNum r + (gNum * 2 ^ r - blk * wBit27 kv s4 r)

def wBitMaxSum27 (kv s4 : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 => wBitMaxSum27 kv s4 r + wBit27 kv s4 r

theorem bitLin27_le_wBitMaxSum27 (kv s4 i : ℕ) :
    ∀ r, bitLin27 kv s4 i r ≤ wBitMaxSum27 kv s4 r
  | 0 => le_rfl
  | r + 1 => by
    unfold bitLin27 wBitMaxSum27
    have ih := bitLin27_le_wBitMaxSum27 kv s4 i r
    cases i.testBit r <;> simp only [cond] <;> omega

theorem bitLin27_envelope_mod (kv s4 blk gNum i : ℕ) :
    ∀ r, blk * bitLin27 kv s4 i r ≤ gNum * (i % 2 ^ r) + dMaxSum27 kv s4 blk gNum r ∧
         gNum * (i % 2 ^ r) ≤ blk * bitLin27 kv s4 i r + dMinAbsSum27 kv s4 blk gNum r
  | 0 => by simp [bitLin27, dMaxSum27, dMinAbsSum27, Nat.mod_one]
  | r + 1 => by
    obtain ⟨ih1, ih2⟩ := bitLin27_envelope_mod kv s4 blk gNum i r
    rw [mod_pow_succ_eq_add_cond, bitLin27, dMaxSum27, dMinAbsSum27]
    cases i.testBit r <;> simp only [cond, zero_add, add_zero]
    · constructor <;> omega
    · rw [Nat.mul_add, Nat.mul_add]
      constructor <;> omega

theorem bitLin27_envelope {kv s4 b_sub gNum i : ℕ} (hi : i < 2 ^ b_sub) :
    2 ^ b_sub * bitLin27 kv s4 i b_sub ≤
      gNum * i + dMaxSum27 kv s4 (2 ^ b_sub) gNum b_sub ∧
    gNum * i ≤
      2 ^ b_sub * bitLin27 kv s4 i b_sub + dMinAbsSum27 kv s4 (2 ^ b_sub) gNum b_sub := by
  have h := bitLin27_envelope_mod kv s4 (2 ^ b_sub) gNum i b_sub
  rwa [Nat.mod_eq_of_lt hi] at h

def leafOK25 : List Leaf25 → Bool
  | [] => true
  | L :: t =>
      let blk := Nat.shiftLeft 1 L.b_sub
      (L.us + L.nsteps * blk == L.ue) &&
      decide (L.ue ≤ 8388608) &&
      (L.us % blk == 0) &&
      wBitOK27 L.kv L.s4 L.b_sub &&
      curvConstOK25 L.s4 L.b_sub &&
      leafOK25 t

theorem leafOK25_append : ∀ (a b : List Leaf25), leafOK25 (a ++ b) = (leafOK25 a && leafOK25 b)
  | [], _ => rfl
  | _ :: t, b => by
      simp only [List.cons_append, leafOK25, leafOK25_append t b, Bool.and_assoc]
private theorem leafOK25_p0 : leafOK25 leafP_0 = true := by decide +kernel
private theorem leafOK25_p1 : leafOK25 leafP_1 = true := by decide +kernel
private theorem leafOK25_p2 : leafOK25 leafP_2 = true := by decide +kernel
private theorem leafOK25_p3 : leafOK25 leafP_3 = true := by decide +kernel
private theorem leafOK25_p4 : leafOK25 leafP_4 = true := by decide +kernel
private theorem leafOK25_p5 : leafOK25 leafP_5 = true := by decide +kernel
private theorem leafOK25_p6 : leafOK25 leafP_6 = true := by decide +kernel
private theorem leafOK25_p7 : leafOK25 leafP_7 = true := by decide +kernel
private theorem leafOK25_p8 : leafOK25 leafP_8 = true := by decide +kernel
private theorem leafOK25_p9 : leafOK25 leafP_9 = true := by decide +kernel
private theorem leafOK25_p10 : leafOK25 leafP_10 = true := by decide +kernel

theorem leafOK25_leafData : leafOK25 leafData25 = true := by
  unfold leafData25
  simp only [leafOK25_append, leafOK25_p0, leafOK25_p1, leafOK25_p2, leafOK25_p3, leafOK25_p4,
    leafOK25_p5, leafOK25_p6, leafOK25_p7, leafOK25_p8, leafOK25_p9, leafOK25_p10, Bool.and_self]

theorem leafOK25_spec : ∀ (ls : List Leaf25), leafOK25 ls = true →
    ∀ L ∈ ls, L.us + L.nsteps * 2 ^ L.b_sub = L.ue ∧ L.ue ≤ 8388608 ∧ L.us % 2 ^ L.b_sub = 0 ∧
      wBitOK27 L.kv L.s4 L.b_sub = true ∧
      curvConstOK25 L.s4 L.b_sub = true
  | [], _, _, hL => absurd hL List.not_mem_nil
  | L :: t, h, L', hL' => by
      dsimp only [leafOK25] at h
      rw [shiftLeft_eq_mul_pow, one_mul] at h
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨hnsteps, hue_le⟩, hus_blk⟩, hw⟩, hc⟩, ht⟩ := h
      rcases List.mem_cons.1 hL' with rfl | hL'
      · exact ⟨hnsteps, hue_le, hus_blk, hw, hc⟩
      · exact leafOK25_spec t ht L' hL'
def PtPosOK25 (L : Leaf25) (u : ℕ) : Prop :=
  |((deltaPos25 L.b_base L.kv L.lv L.s4 u : ℝ) / 2 ^ 23 -
      Real.arcsin ((u : ℝ) / 2 ^ 23))| ≤ 1.25e-7 ∧
  zNeg27 L.kv L.s4 u ≤ zPos27 L.b_base L.kv L.lv L.s4 u ∧
  deltaPos25 L.b_base L.kv L.lv L.s4 u < 2 ^ 24

def stepPt0_25 (zPos zNeg XA : ℕ) (g gn : GS) (k : GS → GS → Bool) : Bool :=
  match adv XA advFuel g gn with
  | (g1, gn1) =>
    let wBase := zPos - zNeg
    let z25 := wBase / 16
    cond (Nat.ble zNeg zPos &&
          Nat.blt z25 16777216 &&
          Nat.ble g1.su XA &&
          Nat.ble (z25 * SCALE37) (ckEPS25 + loB0 g1 gn1 XA) &&
          Nat.ble (hiB g1 gn1 XA) (z25 * SCALE37 + ckEPS25))
      (k g1 gn1)
      false

theorem stepPt0_25_spec {zPos zNeg XA : ℕ} {g gn : GS} {k : GS → GS → Bool}
    (hinv : Inv g gn) (hr : stepPt0_25 zPos zNeg XA g gn k = true) :
    ∃ g1 gn1, Inv g1 gn1 ∧
      zNeg ≤ zPos ∧
      (zPos - zNeg) / 16 < 16777216 ∧
      g1.su ≤ XA ∧
      ((zPos - zNeg) / 16) * SCALE37 ≤ ckEPS25 + loB0 g1 gn1 XA ∧
      hiB g1 gn1 XA ≤ ((zPos - zNeg) / 16) * SCALE37 + ckEPS25 ∧
      k g1 gn1 = true := by
  unfold stepPt0_25 at hr
  have i1 := adv_inv XA advFuel g gn hinv
  generalize adv XA advFuel g gn = p1 at hr i1
  obtain ⟨g1, gn1⟩ := p1
  dsimp only at hr i1
  set wBase := zPos - zNeg
  set z25 := wBase / 16
  cases hc : (Nat.ble zNeg zPos &&
        Nat.blt z25 16777216 &&
        Nat.ble g1.su XA &&
        Nat.ble (z25 * SCALE37) (ckEPS25 + loB0 g1 gn1 XA) &&
        Nat.ble (hiB g1 gn1 XA) (z25 * SCALE37 + ckEPS25))
  · rw [hc, Bool.cond_false] at hr; cases hr
  rw [hc, Bool.cond_true] at hr
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hc
  obtain ⟨⟨⟨⟨hzle, htop⟩, hsuA⟩, hok1⟩, hok2⟩ := hc
  exact ⟨g1, gn1, i1, hzle, htop, hsuA, hok1, hok2, hr⟩

def stepPtsSub_25 (zPos zNeg blk gNum dMax dMinAbs wMax XA XB : ℕ) (g gn : GS)
    (k : GS → GS → Bool) : Bool :=
  match adv XA advFuel g gn with
  | (g1, gn1) =>
    match adv XB advFuel g1 gn1 with
    | (g2, gn2) =>
      let wBase := zPos - zNeg
      cond (Nat.ble zNeg zPos &&
            Nat.blt (wBase + wMax) 268435456 &&
            Nat.ble g1.su XA &&
            Nat.ble ((blk * wBase + dMax) * SCALE33) (blk * (ckEPS25 + loB g1 XA)) &&
            Nat.ble ((blk * wBase + gNum * (blk - 1) + dMax) * SCALE33)
              (blk * (ckEPS25 + loB g1 XB)) &&
            Nat.ble (blk * hiB g1 gn1 XA + (dMinAbs + 15 * blk) * SCALE33)
              (blk * (wBase * SCALE33 + ckEPS25)) &&
            Nat.ble (blk * hiB g2 gn2 XB + (dMinAbs + 15 * blk) * SCALE33)
              ((blk * wBase + gNum * (blk - 1)) * SCALE33 + blk * ckEPS25))
        (k g2 gn2)
        false

theorem stepPtsSub_25_spec {zPos zNeg blk gNum dMax dMinAbs wMax XA XB : ℕ} {g gn : GS}
    {k : GS → GS → Bool} (hinv : Inv g gn)
    (hr : stepPtsSub_25 zPos zNeg blk gNum dMax dMinAbs wMax XA XB g gn k = true) :
    ∃ g1 gn1 g2 gn2, Inv g1 gn1 ∧ Inv g2 gn2 ∧
      zNeg ≤ zPos ∧
      (zPos - zNeg) + wMax < 268435456 ∧
      g1.su ≤ XA ∧
      (blk * (zPos - zNeg) + dMax) * SCALE33 ≤ blk * (ckEPS25 + loB g1 XA) ∧
      (blk * (zPos - zNeg) + gNum * (blk - 1) + dMax) * SCALE33 ≤ blk * (ckEPS25 + loB g1 XB) ∧
      blk * hiB g1 gn1 XA + (dMinAbs + 15 * blk) * SCALE33 ≤
        blk * ((zPos - zNeg) * SCALE33 + ckEPS25) ∧
      blk * hiB g2 gn2 XB + (dMinAbs + 15 * blk) * SCALE33 ≤
        (blk * (zPos - zNeg) + gNum * (blk - 1)) * SCALE33 + blk * ckEPS25 ∧
      k g2 gn2 = true := by
  unfold stepPtsSub_25 at hr
  have i1 := adv_inv XA advFuel g gn hinv
  generalize adv XA advFuel g gn = p1 at hr i1
  obtain ⟨g1, gn1⟩ := p1
  dsimp only at hr i1
  have i2 := adv_inv XB advFuel g1 gn1 i1
  generalize adv XB advFuel g1 gn1 = p2 at hr i2
  obtain ⟨g2, gn2⟩ := p2
  dsimp only at hr i2
  set wBase := zPos - zNeg
  cases hc : (Nat.ble zNeg zPos &&
            Nat.blt (wBase + wMax) 268435456 &&
            Nat.ble g1.su XA &&
            Nat.ble ((blk * wBase + dMax) * SCALE33) (blk * (ckEPS25 + loB g1 XA)) &&
            Nat.ble ((blk * wBase + gNum * (blk - 1) + dMax) * SCALE33)
              (blk * (ckEPS25 + loB g1 XB)) &&
            Nat.ble (blk * hiB g1 gn1 XA + (dMinAbs + 15 * blk) * SCALE33)
              (blk * (wBase * SCALE33 + ckEPS25)) &&
            Nat.ble (blk * hiB g2 gn2 XB + (dMinAbs + 15 * blk) * SCALE33)
              ((blk * wBase + gNum * (blk - 1)) * SCALE33 + blk * ckEPS25))
  · rw [hc, Bool.cond_false] at hr; cases hr
  rw [hc, Bool.cond_true] at hr
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨hzle, htop⟩, hsuA⟩, hok1⟩, hok2⟩, hok3⟩, hok4⟩ := hc
  exact ⟨g1, gn1, g2, gn2, i1, i2, hzle, htop, hsuA, hok1, hok2, hok3, hok4, hr⟩

def stepBlockPos25 (u : ℕ) (L : Leaf25) (g gn : GS) (k : GS → GS → Bool) : Bool :=
  cond (Nat.beq L.b_sub 0)
    (stepPt0_25
      (zPos27 L.b_base L.kv L.lv L.s4 u)
      (zNeg27 L.kv L.s4 u)
      (u * SCALE37) g gn k)
    (let blk := Nat.shiftLeft 1 L.b_sub
     let dMax := dMaxSum27 L.kv L.s4 blk L.gNum L.b_sub
     let dMinAbs := dMinAbsSum27 L.kv L.s4 blk L.gNum L.b_sub
     let wMax := wBitMaxSum27 L.kv L.s4 L.b_sub
     stepPtsSub_25
       (zPos27 L.b_base L.kv L.lv L.s4 u)
       (zNeg27 L.kv L.s4 u)
       blk L.gNum dMax dMinAbs wMax
       (u * SCALE37) ((u + blk - 1) * SCALE37) g gn k)

theorem stepBlockPos25_sound {L : Leaf25} (hL : L ∈ leafData25) {u : ℕ}
    (_ : L.us ≤ u) (hu2 : u + 2 ^ L.b_sub ≤ L.ue) (hu_mod : u % 2 ^ L.b_sub = 0)
    {g gn : GS} (hinv : Inv g gn) {k : GS → GS → Bool}
    (hr : stepBlockPos25 u L g gn k = true) :
    ∃ g2 gn2, Inv g2 gn2 ∧ k g2 gn2 = true ∧ ∀ i < 2 ^ L.b_sub, PtPosOK25 L (u + i) := by
  obtain ⟨_, hue_le, _, hw, hc⟩ := leafOK25_spec leafData25 leafOK25_leafData L hL
  unfold stepBlockPos25 at hr
  cases hb0 : Nat.beq L.b_sub 0
  · rw [hb0, Bool.cond_false] at hr
    dsimp only at hr
    rw [shiftLeft_eq_mul_pow, one_mul] at hr
    obtain ⟨g1, gn1, g2, gn2, i1, i2, hzle, htop, hsuA, hok1, hok2, hok3, hok4, hr_k⟩ :=
      stepPtsSub_25_spec hinv hr
    have hb_pos : 0 < L.b_sub := by
      have hne : L.b_sub ≠ 0 := fun h => by rw [h] at hb0; cases hb0
      omega
    set blk := 2 ^ L.b_sub
    have hblk2 : 2 ≤ blk := by
      have : 2 ^ 1 ≤ 2 ^ L.b_sub := Nat.pow_le_pow_right (by omega) hb_pos
      omega
    have hblk_pos_r : (0 : ℝ) < blk := by positivity
    set wBase := diff27 L.b_base L.kv L.lv L.s4 u with hwBase
    set XA := u * SCALE37
    set XB := (u + blk - 1) * SCALE37
    have hsuB : g1.su ≤ XB := hsuA.trans (Nat.mul_le_mul_right SCALE37 (by omega))
    refine ⟨g2, gn2, i2, hr_k, fun i hi => ?_⟩
    obtain ⟨hzle_i, hw_i⟩ := diff27_add_eq hw hc hu_mod hi hzle
    have hbit_le := bitLin27_le_wBitMaxSum27 L.kv L.s4 i L.b_sub
    have hlt_24 : deltaPos25 L.b_base L.kv L.lv L.s4 (u + i) < 2 ^ 24 := by
      unfold deltaPos25
      rw [hw_i]
      unfold diff27 at hwBase
      omega
    refine ⟨?_, hzle_i, hlt_24⟩
    obtain ⟨henv_max, henv_min⟩ := bitLin27_envelope (gNum := L.gNum) hi
    set bL := bitLin27 L.kv L.s4 i L.b_sub
    set dMax := dMaxSum27 L.kv L.s4 blk L.gNum L.b_sub
    set dMinAbs := dMinAbsSum27 L.kv L.s4 blk L.gNum L.b_sub
    set z_i := deltaPos25 L.b_base L.kv L.lv L.s4 (u + i)
    have hz_i_le : 16 * z_i ≤ wBase + bL := by
      dsimp only [z_i, deltaPos25]; rw [hw_i]; exact Nat.mul_div_le _ 16
    have hw_i_le : wBase + bL ≤ 16 * z_i + 15 := by
      dsimp only [z_i, deltaPos25]; rw [hw_i]; omega
    have hu_le : u + blk ≤ 8388608 := hu2.trans hue_le
    have h1_r :
        ((blk * wBase + dMax : ℕ) : ℝ) / 2 ^ 27 ≤ (blk : ℝ) * (sc ckEPS25 + sc (loB g1 XA)) := by
      have := sc_mono hok1
      rwa [sc_mul33, sc_mul_nat, sc_add] at this
    have h2_r : ((blk * wBase + L.gNum * (blk - 1) + dMax : ℕ) : ℝ) / 2 ^ 27 ≤
        (blk : ℝ) * (sc ckEPS25 + sc (loB g1 XB)) := by
      have := sc_mono hok2
      rwa [sc_mul33, sc_mul_nat, sc_add] at this
    have h3_r : (blk : ℝ) * sc (hiB g1 gn1 XA) + ((dMinAbs + 15 * blk : ℕ) : ℝ) / 2 ^ 27 ≤
        (blk : ℝ) * ((wBase : ℝ) / 2 ^ 27 + sc ckEPS25) := by
      have := sc_mono hok3
      rwa [sc_add, sc_mul_nat, sc_mul33, sc_mul_nat, sc_add, sc_mul33] at this
    have h4_r : (blk : ℝ) * sc (hiB g2 gn2 XB) + ((dMinAbs + 15 * blk : ℕ) : ℝ) / 2 ^ 27 ≤
        ((blk * wBase + L.gNum * (blk - 1) : ℕ) : ℝ) / 2 ^ 27 + (blk : ℝ) * sc ckEPS25 := by
      have := sc_mono hok4
      rwa [sc_add, sc_mul_nat, sc_mul33, sc_add, sc_mul33, sc_mul_nat] at this
    have hhA := hiB_sound i1 XA
    have hhB := hiB_sound i2 XB
    set N : ℕ := blk - 1
    have hN_pos : (0 : ℝ) < N := by
      have : 1 ≤ N := by omega
      exact_mod_cast this
    have hi_le_N : i ≤ N := by omega
    set a : ℝ := ((N - i : ℕ) : ℝ) / (N : ℝ)
    set b : ℝ := (i : ℝ) / (N : ℝ)
    have ha : 0 ≤ a := div_nonneg (Nat.cast_nonneg _) hN_pos.le
    have hb : 0 ≤ b := div_nonneg (Nat.cast_nonneg _) hN_pos.le
    have hab : a + b = 1 := by
      dsimp only [a, b]
      rw [← add_div, Nat.cast_sub hi_le_N, sub_add_cancel, div_self hN_pos.ne']
    have hN_mul_b : (N : ℝ) * b = (i : ℝ) := mul_div_cancel₀ _ hN_pos.ne'
    have hX_comb : a * sc XA + b * sc XB = ((u + i : ℕ) : ℝ) / 2 ^ 23 := by
      rw [sc_mul37, sc_mul37]
      have hXB_eq : ((u + blk - 1 : ℕ) : ℝ) = (u : ℝ) + (N : ℝ) := by
        rw [show u + blk - 1 = u + N by omega]; push_cast; rfl
      rw [hXB_eq]; push_cast
      calc a * ((u : ℝ) / 2 ^ 23) + b * (((u : ℝ) + N) / 2 ^ 23)
          = ((a + b) * (u : ℝ) + (N : ℝ) * b) / 2 ^ 23 := by ring
        _ = ((u : ℝ) + (i : ℝ)) / 2 ^ 23 := by rw [hab, one_mul, hN_mul_b]
    have hlo := loB_secant_sound i1.1 hsuA hsuB ha hb hab
    rw [hX_comb] at hlo
    have hXA0 : 0 ≤ sc XA := sc_nonneg XA
    have hXB0 : 0 ≤ sc XB := sc_nonneg XB
    have hXB1 : sc XB ≤ 1 := by
      rw [sc_mul37, div_le_one (by positivity)]
      have : u + blk - 1 ≤ 8388608 := by omega
      exact_mod_cast this
    have hXA1 : sc XA ≤ 1 := (sc_mono (Nat.mul_le_mul_right SCALE37 (by omega))).trans hXB1
    have hsec := arcsin_secant_sound hXA0 hXA1 hXB0 hXB1 ha hb hab
    rw [hX_comb] at hsec
    have hhi_comb :
        arcsin (((u + i : ℕ) : ℝ) / 2 ^ 23) ≤ a * sc (hiB g1 gn1 XA) + b * sc (hiB g2 gn2 XB) :=
      hsec.trans (add_le_add (mul_le_mul_of_nonneg_left hhA ha) (mul_le_mul_of_nonneg_left hhB hb))
    have henv_max_r : (blk : ℝ) * (bL : ℝ) ≤ (L.gNum : ℝ) * (i : ℝ) + (dMax : ℝ) := by
      exact_mod_cast henv_max
    have henv_min_r : (L.gNum : ℝ) * (i : ℝ) ≤ (blk : ℝ) * (bL : ℝ) + (dMinAbs : ℝ) := by
      exact_mod_cast henv_min
    have hz_i_le_r : 16 * (z_i : ℝ) ≤ (wBase : ℝ) + (bL : ℝ) := by exact_mod_cast hz_i_le
    have hw_i_le_r : (wBase : ℝ) + (bL : ℝ) ≤ 16 * (z_i : ℝ) + 15 := by exact_mod_cast hw_i_le
    push_cast at h1_r h2_r h3_r h4_r
    have hc12 := add_le_add (mul_le_mul_of_nonneg_left h1_r ha) (mul_le_mul_of_nonneg_left h2_r hb)
    have hc34 := add_le_add (mul_le_mul_of_nonneg_left h3_r ha) (mul_le_mul_of_nonneg_left h4_r hb)
    have h_lhs12 : a * (((blk : ℝ) * wBase + dMax) / 2 ^ 27) +
                   b * (((blk : ℝ) * wBase + (L.gNum : ℝ) * (N : ℝ) + dMax) / 2 ^ 27) =
                   ((blk : ℝ) * wBase + (L.gNum : ℝ) * (i : ℝ) + dMax) / 2 ^ 27 := by
      calc a * (((blk : ℝ) * wBase + dMax) / 2 ^ 27) +
           b * (((blk : ℝ) * wBase + (L.gNum : ℝ) * (N : ℝ) + dMax) / 2 ^ 27)
          = ((a + b) * ((blk : ℝ) * wBase + dMax) + (L.gNum : ℝ) * ((N : ℝ) * b)) / 2 ^ 27 := by
              ring
        _ = ((blk : ℝ) * wBase + (L.gNum : ℝ) * (i : ℝ) + dMax) / 2 ^ 27 := by
              rw [hab, hN_mul_b]
              ring
    have h_rhs12 : a * ((blk : ℝ) * (sc ckEPS25 + sc (loB g1 XA))) +
                   b * ((blk : ℝ) * (sc ckEPS25 + sc (loB g1 XB))) =
                   (blk : ℝ) * (sc ckEPS25 + (a * sc (loB g1 XA) + b * sc (loB g1 XB))) := by
      calc a * ((blk : ℝ) * (sc ckEPS25 + sc (loB g1 XA))) +
           b * ((blk : ℝ) * (sc ckEPS25 + sc (loB g1 XB)))
          = (blk : ℝ) * ((a + b) * sc ckEPS25 + (a * sc (loB g1 XA) + b * sc (loB g1 XB))) := by
              ring
        _ = (blk : ℝ) * (sc ckEPS25 + (a * sc (loB g1 XA) + b * sc (loB g1 XB))) := by
              rw [hab, one_mul]
    rw [h_lhs12, h_rhs12] at hc12
    have h_lhs34 : a * ((blk : ℝ) * sc (hiB g1 gn1 XA) + ((dMinAbs : ℝ) + 15 * blk) / 2 ^ 27) +
                   b * ((blk : ℝ) * sc (hiB g2 gn2 XB) + ((dMinAbs : ℝ) + 15 * blk) / 2 ^ 27) =
                   (blk : ℝ) * (a * sc (hiB g1 gn1 XA) + b * sc (hiB g2 gn2 XB)) +
                     ((dMinAbs : ℝ) + 15 * blk) / 2 ^ 27 := by
      calc a * ((blk : ℝ) * sc (hiB g1 gn1 XA) + ((dMinAbs : ℝ) + 15 * blk) / 2 ^ 27) +
           b * ((blk : ℝ) * sc (hiB g2 gn2 XB) + ((dMinAbs : ℝ) + 15 * blk) / 2 ^ 27)
          = (blk : ℝ) * (a * sc (hiB g1 gn1 XA) + b * sc (hiB g2 gn2 XB)) +
              (a + b) * (((dMinAbs : ℝ) + 15 * blk) / 2 ^ 27) := by
              ring
        _ = (blk : ℝ) * (a * sc (hiB g1 gn1 XA) + b * sc (hiB g2 gn2 XB)) +
              ((dMinAbs : ℝ) + 15 * blk) / 2 ^ 27 := by
              rw [hab, one_mul]
    have h_rhs34 : a * ((blk : ℝ) * ((wBase : ℝ) / 2 ^ 27 + sc ckEPS25)) +
                   b * (((blk : ℝ) * wBase + (L.gNum : ℝ) * (N : ℝ)) / 2 ^ 27 +
                     (blk : ℝ) * sc ckEPS25) =
                   ((blk : ℝ) * wBase + (L.gNum : ℝ) * (i : ℝ)) / 2 ^ 27 +
                     (blk : ℝ) * sc ckEPS25 := by
      calc a * ((blk : ℝ) * ((wBase : ℝ) / 2 ^ 27 + sc ckEPS25)) +
           b * (((blk : ℝ) * wBase + (L.gNum : ℝ) * (N : ℝ)) / 2 ^ 27 + (blk : ℝ) * sc ckEPS25)
          = ((a + b) * (blk : ℝ) * wBase + (L.gNum : ℝ) * ((N : ℝ) * b)) / 2 ^ 27 +
              (a + b) * (blk : ℝ) * sc ckEPS25 := by
              ring
        _ = ((blk : ℝ) * wBase + (L.gNum : ℝ) * (i : ℝ)) / 2 ^ 27 +
              (blk : ℝ) * sc ckEPS25 := by
              rw [hab, hN_mul_b]
              ring
    rw [h_lhs34, h_rhs34] at hc34
    change |(z_i : ℝ) / 2 ^ 23 - arcsin (((u + i : ℕ) : ℝ) / 2 ^ 23)| ≤ 1.25e-7
    rw [abs_le]
    constructor
    · have h_mul : (blk : ℝ) * arcsin (((u + i : ℕ) : ℝ) / 2 ^ 23) ≤
          (blk : ℝ) * ((z_i : ℝ) / 2 ^ 23 + sc ckEPS25) := by
        have hstep1 := mul_le_mul_of_nonneg_left hhi_comb hblk_pos_r.le
        have hstep2 :
            ((blk : ℝ) * wBase + (L.gNum : ℝ) * (i : ℝ) - ((dMinAbs : ℝ) + 15 * blk)) / 2 ^ 27 ≤
              (blk : ℝ) * ((z_i : ℝ) / 2 ^ 23) := by
          have h_alg : (blk : ℝ) * ((z_i : ℝ) / 2 ^ 23) -
                 (((blk : ℝ) * wBase + (L.gNum : ℝ) * (i : ℝ) -
                   ((dMinAbs : ℝ) + 15 * blk)) / 2 ^ 27) =
                 ((blk : ℝ) * (16 * (z_i : ℝ) + 15 - ((wBase : ℝ) + bL)) +
                  ((blk : ℝ) * bL + dMinAbs - (L.gNum : ℝ) * i)) / 2 ^ 27 := by ring
          have h_n1 : 0 ≤ (blk : ℝ) * (16 * (z_i : ℝ) + 15 - ((wBase : ℝ) + bL)) :=
            mul_nonneg hblk_pos_r.le (by linarith)
          have h_n2 : 0 ≤ (blk : ℝ) * bL + dMinAbs - (L.gNum : ℝ) * i := by linarith
          linarith [div_nonneg (add_nonneg h_n1 h_n2) (by positivity : (0 : ℝ) ≤ 2 ^ 27)]
        linarith
      have h_div := le_of_mul_le_mul_left h_mul hblk_pos_r
      linarith [sc_ckEPS25]
    · have h_mul : (blk : ℝ) * ((z_i : ℝ) / 2 ^ 23) ≤
          (blk : ℝ) * (sc ckEPS25 + arcsin (((u + i : ℕ) : ℝ) / 2 ^ 23)) := by
        have hstep1 : (blk : ℝ) * ((z_i : ℝ) / 2 ^ 23) ≤
            ((blk : ℝ) * wBase + (L.gNum : ℝ) * (i : ℝ) + dMax) / 2 ^ 27 := by
          have h_alg : (((blk : ℝ) * wBase + (L.gNum : ℝ) * (i : ℝ) + dMax) / 2 ^ 27) -
                 (blk : ℝ) * ((z_i : ℝ) / 2 ^ 23) =
                 ((blk : ℝ) * ((wBase : ℝ) + bL - 16 * (z_i : ℝ)) +
                  ((L.gNum : ℝ) * i + dMax - (blk : ℝ) * bL)) / 2 ^ 27 := by ring
          have h_n1 : 0 ≤ (blk : ℝ) * ((wBase : ℝ) + bL - 16 * (z_i : ℝ)) :=
            mul_nonneg hblk_pos_r.le (by linarith)
          have h_n2 : 0 ≤ (L.gNum : ℝ) * i + dMax - (blk : ℝ) * bL := by linarith
          linarith [div_nonneg (add_nonneg h_n1 h_n2) (by positivity : (0 : ℝ) ≤ 2 ^ 27)]
        have hstep2 := mul_le_mul_of_nonneg_left hlo hblk_pos_r.le
        linarith
      have h_div := le_of_mul_le_mul_left h_mul hblk_pos_r
      linarith [sc_ckEPS25]
  · rw [hb0, Bool.cond_true] at hr
    have hb_eq : L.b_sub = 0 := Nat.beq_eq.mp hb0
    obtain ⟨g1, gn1, i1, hzle, htop, hsuA, hok1, hok2, hr_k⟩ := stepPt0_25_spec hinv hr
    refine ⟨g1, gn1, i1, hr_k, fun i hi => ?_⟩
    rw [hb_eq] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    rw [Nat.add_zero]
    set z25 := deltaPos25 L.b_base L.kv L.lv L.s4 u
    change |((z25 : ℝ) / 2 ^ 23 - Real.arcsin ((u : ℝ) / 2 ^ 23))| ≤ 1.25e-7 ∧
      zNeg27 L.kv L.s4 u ≤ zPos27 L.b_base L.kv L.lv L.s4 u ∧ z25 < 2 ^ 24
    have hlt_24 : z25 < 2 ^ 24 := htop
    refine ⟨?_, hzle, hlt_24⟩
    have h1_r : (z25 : ℝ) / 2 ^ 23 ≤ sc ckEPS25 + sc (loB0 g1 gn1 (u * SCALE37)) := by
      have := sc_mono hok1
      rwa [sc_mul37, sc_add] at this
    have h2_r : sc (hiB g1 gn1 (u * SCALE37)) ≤ (z25 : ℝ) / 2 ^ 23 + sc ckEPS25 := by
      have := sc_mono hok2
      rwa [sc_add, sc_mul37] at this
    have hlo0 := loB0_sound_pt i1 (u * SCALE37)
    have hhi0 := hiB_sound i1 (u * SCALE37)
    rw [sc_mul37] at hlo0 hhi0
    rw [abs_le]
    constructor <;> linarith [sc_ckEPS25]

def walkLeafPos25 (L : Leaf25) : ℕ → ℕ → GS → GS → (GS → GS → Bool) → Bool
  | 0, _, g, gn, k => k g gn
  | n + 1, u, g, gn, k =>
      stepBlockPos25 u L g gn fun g' gn' =>
        walkLeafPos25 L n (u + Nat.shiftLeft 1 L.b_sub) g' gn' k

def walkLeavesPos25 : List Leaf25 → GS → GS → Bool
  | [], _, _ => true
  | L :: ls, g, gn => walkLeafPos25 L L.nsteps L.us g gn fun g' gn' => walkLeavesPos25 ls g' gn'


def forceNatNat (v : ℕ) (k : ℕ → ℕ) : ℕ :=
  match v with
  | 0 => k 0
  | n + 1 => k (n + 1)

theorem forceNatNat_eq (v : ℕ) (k : ℕ → ℕ) : forceNatNat v k = k v := by
  cases v <;> rfl

def forceNatBool (v : ℕ) (k : ℕ → Bool) : Bool :=
  match v with
  | 0 => k 0
  | n + 1 => k (n + 1)

theorem forceNatBool_eq (v : ℕ) (k : ℕ → Bool) : forceNatBool v k = k v := by
  cases v <;> rfl

def forceBoolBool (b : Bool) (k : Bool → Bool) : Bool :=
  match b with
  | false => k false
  | true => k true

theorem forceBoolBool_eq (b : Bool) (k : Bool → Bool) : forceBoolBool b k = k b := by
  cases b <;> rfl

def loBFast (g : GS) (XP : ℕ) : ℕ :=
  cond (Nat.ble g.su XP)
    (forceNatNat (Nat.add (Nat.mul g.i ckH) (Nat.div (Nat.mul (Nat.sub XP g.su) ckOne) g.cu))
      fun v => min v ckPI2L) 0

theorem loBFast_eq (g : GS) (XP : ℕ) : loBFast g XP = loB g XP := by
  unfold loBFast loB
  simp only [forceNatNat_eq]

def loB0Fast (g gn : GS) (XP : ℕ) : ℕ :=
  max (loBFast g XP) (loB_gn g gn XP)

theorem loB0Fast_eq (g gn : GS) (XP : ℕ) : loB0Fast g gn XP = loB0 g gn XP := by
  unfold loB0Fast loB0
  rw [loBFast_eq]

def ckOneSq : ℕ := 1329227995784915872903807060280344576

theorem ckOneSq_eq : ckOneSq = Nat.mul ckOne ckOne := rfl

def hiBDFast (gn : GS) (XP D : ℕ) : ℕ :=
  forceNatNat (Nat.mul gn.i ckH) fun iH =>
  cond (and (Nat.ble (Nat.add (Nat.mul (Nat.mul 2 XP) ckOneSq)
      (Nat.add (Nat.mul gn.su (Nat.mul D D)) (Nat.mul (Nat.mul 2 gn.cu) (Nat.mul D ckOne))))
      (Nat.mul (Nat.mul 2 gn.sl) ckOneSq))
    (Nat.ble D iH))
    (Nat.sub iH D) ckPI2U

theorem hiBDFast_eq (gn : GS) (XP D : ℕ) : hiBDFast gn XP D = hiB.hiBD gn XP D := by
  unfold hiBDFast hiB.hiBD
  simp only [forceNatNat_eq, ckOneSq_eq]

def hiBFast (g gn : GS) (XP : ℕ) : ℕ :=
  cond (and (Nat.blt g.i ckN) (Nat.ble XP gn.sl))
    (forceNatNat
      (Nat.div (Nat.mul (Nat.sub gn.sl XP) ckOne) (Nat.add gn.cu (Nat.div gn.su 262144)))
      fun D => hiBDFast gn XP D)
    ckPI2U

theorem hiBFast_eq (g gn : GS) (XP : ℕ) : hiBFast g gn XP = hiB g gn XP := by
  unfold hiBFast hiB
  simp only [forceNatNat_eq, hiBDFast_eq]

theorem cond_testBit_eq_div_mod (w t : ℕ) : cond (w.testBit t) 1 0 = (w / 2 ^ t) % 2 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (w / 2 ^ t) with h | h <;> simp [h]

theorem nat_add_eq (a b : ℕ) : Nat.add a b = a + b := rfl
theorem nat_sub_eq (a b : ℕ) : Nat.sub a b = a - b := rfl
theorem nat_mul_eq (a b : ℕ) : Nat.mul a b = a * b := rfl
theorem nat_div_eq (a b : ℕ) : Nat.div a b = a / b := rfl

theorem land_shiftRight_one_eq_div_mod (w t : ℕ) :
    Nat.land (Nat.shiftRight w t) 1 = (w / 2 ^ t) % 2 := by
  change (w >>> t) &&& 1 = (w / 2 ^ t) % 2
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

def uRotBitFast4 (u src : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight u src) 1

theorem uRotBitFast4_eq (u s4 j : ℕ) :
    uRotBitFast4 u (uRotSrc s4 j) = cond (uRotBit u s4 j) 1 0 := by
  unfold uRotBitFast4 uRotBit
  rw [land_shiftRight_one_eq_div_mod, ← cond_testBit_eq_div_mod]

def d9Fast4 (v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) : ℕ :=
  let raw9 := Nat.add v6 (Nat.add (Nat.mul 2 v7) (Nat.add (Nat.mul 4 v8) (Nat.add (Nat.mul 8 v9)
    (Nat.add (Nat.mul 16 v10) (Nat.add (Nat.mul 32 v11) (Nat.add (Nat.mul 64 v12)
      (Nat.add (Nat.mul 128 v13) (Nat.mul 256 v14))))))))
  cond (Nat.beq v15 1) raw9 (Nat.sub 511 raw9)

theorem d9Fast4_eq (u s4 : ℕ) :
    d9Fast4 (cond (uRotBit u s4 6) 1 0) (cond (uRotBit u s4 7) 1 0)
      (cond (uRotBit u s4 8) 1 0) (cond (uRotBit u s4 9) 1 0)
      (cond (uRotBit u s4 10) 1 0) (cond (uRotBit u s4 11) 1 0)
      (cond (uRotBit u s4 12) 1 0) (cond (uRotBit u s4 13) 1 0)
      (cond (uRotBit u s4 14) 1 0) (cond (uRotBit u s4 15) 1 0) =
    d9Val u s4 := by
  unfold d9Fast4 d9Val
  dsimp only
  have h15 : Nat.beq (cond (uRotBit u s4 15) 1 0) 1 = uRotBit u s4 15 := by
    cases uRotBit u s4 15 <;> rfl
  have hraw : Nat.add (cond (uRotBit u s4 6) 1 0)
    (Nat.add (Nat.mul 2 (cond (uRotBit u s4 7) 1 0))
    (Nat.add (Nat.mul 4 (cond (uRotBit u s4 8) 1 0))
    (Nat.add (Nat.mul 8 (cond (uRotBit u s4 9) 1 0))
    (Nat.add (Nat.mul 16 (cond (uRotBit u s4 10) 1 0))
    (Nat.add (Nat.mul 32 (cond (uRotBit u s4 11) 1 0))
    (Nat.add (Nat.mul 64 (cond (uRotBit u s4 12) 1 0))
    (Nat.add (Nat.mul 128 (cond (uRotBit u s4 13) 1 0))
      (Nat.mul 256 (cond (uRotBit u s4 14) 1 0))))))))) = evalBits (uRotBit u s4) 6 9 := by
    simp only [evalBits, shiftLeft_eq_mul_pow, nat_add_eq, nat_mul_eq]
    ring
  rw [h15, nat_sub_eq, hraw]

def curvFromSq9Fast4 (c0 c1 c2 c3 c4 c5 c6 c7 : Bool) (sq9 : ℕ) : ℕ :=
  let sl0 := Nat.div sq9 128
  let sl1 := Nat.div sq9 64
  let sl2 := Nat.div sq9 32
  let sl3 := Nat.div sq9 16
  let sl4 := Nat.div sq9 8
  let sl5 := Nat.div sq9 4
  let sl6 := Nat.div sq9 2
  let sl7 := Nat.div sq9 1
  Nat.add (Nat.mul 2 sq9)
    (Nat.add (cond c0 (Nat.sub 3 sl0) sl0)
      (Nat.add (cond c1 (Nat.sub 7 sl1) sl1)
        (Nat.add (cond c2 (Nat.sub 15 sl2) sl2)
          (Nat.add (cond c3 (Nat.sub 31 sl3) sl3)
            (Nat.add (cond c4 (Nat.sub 63 sl4) sl4)
              (Nat.add (cond c5 (Nat.sub 127 sl5) sl5)
                (Nat.add (cond c6 (Nat.sub 255 sl6) sl6)
                  (cond c7 (Nat.sub 511 sl7) sl7))))))))

theorem curvFromSq9Fast4_eq (lv sq9 : ℕ) :
    curvFromSq9Fast4 (lv.testBit 0) (lv.testBit 1) (lv.testBit 2) (lv.testBit 3)
      (lv.testBit 4) (lv.testBit 5) (lv.testBit 6) (lv.testBit 7) sq9 =
    curvFromSq9 lv sq9 := by
  unfold curvFromSq9Fast4 curvFromSq9 curvTerm
  dsimp only
  simp only [nat_add_eq, nat_sub_eq, nat_mul_eq, nat_div_eq]
  ring

def sq9ValFast4 (w0 w1 w2 w3 w4 w5 w6 w7 w8 d9 : ℕ) : ℕ :=
  Nat.add (Nat.land (Nat.shiftRight w0 d9) 1)
    (Nat.add (Nat.mul 2 (Nat.land (Nat.shiftRight w1 d9) 1))
      (Nat.add (Nat.mul 4 (Nat.land (Nat.shiftRight w2 d9) 1))
        (Nat.add (Nat.mul 8 (Nat.land (Nat.shiftRight w3 d9) 1))
          (Nat.add (Nat.mul 16 (Nat.land (Nat.shiftRight w4 d9) 1))
            (Nat.add (Nat.mul 32 (Nat.land (Nat.shiftRight w5 d9) 1))
              (Nat.add (Nat.mul 64 (Nat.land (Nat.shiftRight w6 d9) 1))
                (Nat.add (Nat.mul 128 (Nat.land (Nat.shiftRight w7 d9) 1))
                  (Nat.mul 256 (Nat.land (Nat.shiftRight w8 d9) 1)))))))))

theorem sq9ValFast4_eq (d9 : ℕ) :
    sq9ValFast4 (sq9Words.getD 0 0) (sq9Words.getD 1 0) (sq9Words.getD 2 0)
      (sq9Words.getD 3 0) (sq9Words.getD 4 0) (sq9Words.getD 5 0)
      (sq9Words.getD 6 0) (sq9Words.getD 7 0) (sq9Words.getD 8 0) d9 =
    sq9Val d9 := by
  unfold sq9ValFast4 sq9Val
  simp only [evalBits, Nat.zero_add, cond_testBit_eq_div_mod, shiftLeft_eq_mul_pow,
    land_shiftRight_one_eq_div_mod, nat_add_eq, nat_mul_eq]
  ring
def spBase27 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) : ℕ :=
  4 * (v0 + 2 * v1 + 4 * v2 + 8 * v3 + 16 * v4 + 32 * v5 + 64 * v6 + 128 * v7 + 256 * v8 +
    512 * v9 + 1024 * v10 + 2048 * v11 + 4096 * v12 + 8192 * v13 + 16384 * v14 + 32768 * v15)
theorem spBase27_eq (u s4 : ℕ) :
    spBase27 (cond (uRotBit u s4 0) 1 0) (cond (uRotBit u s4 1) 1 0)
      (cond (uRotBit u s4 2) 1 0) (cond (uRotBit u s4 3) 1 0) (cond (uRotBit u s4 4) 1 0)
      (cond (uRotBit u s4 5) 1 0) (cond (uRotBit u s4 6) 1 0) (cond (uRotBit u s4 7) 1 0)
      (cond (uRotBit u s4 8) 1 0) (cond (uRotBit u s4 9) 1 0) (cond (uRotBit u s4 10) 1 0)
      (cond (uRotBit u s4 11) 1 0) (cond (uRotBit u s4 12) 1 0) (cond (uRotBit u s4 13) 1 0)
      (cond (uRotBit u s4 14) 1 0) (cond (uRotBit u s4 15) 1 0) =
    4 * evalBits (uRotBit u s4) 0 16 := by
  unfold spBase27
  simp only [evalBits, shiftLeft_eq_mul_pow]
  ring
theorem spBase27_lin (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : ℕ) :
    spBase27 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 =
      spBase27 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 * v0 +
      spBase27 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 * v1 +
      spBase27 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 * v2 +
      spBase27 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 * v3 +
      spBase27 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 * v4 +
      spBase27 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 * v5 +
      spBase27 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 * v6 +
      spBase27 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 * v7 +
      spBase27 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 * v8 +
      spBase27 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 * v9 +
      spBase27 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 * v10 +
      spBase27 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 * v11 +
      spBase27 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 * v12 +
      spBase27 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 * v13 +
      spBase27 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 * v14 +
      spBase27 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 * v15 := by
  unfold spBase27
  ring
def spPos27_0 (b : Bool) (v13 v14 v15 : ℕ) : ℕ :=
  cond b ((v13 + 2 * v14 + 4 * v15) * 1) 0
def spNeg27_0 (b : Bool) (v13 v14 v15 : ℕ) : ℕ := cond (!b) ((v13 + 2 * v14 + 4 * v15) * 1) 0
theorem spPos27_0_eq (kv u s4 : ℕ) :
    spPos27_0 (kv.testBit 0) (cond (uRotBit u s4 13) 1 0) (cond (uRotBit u s4 14) 1 0)
      (cond (uRotBit u s4 15) 1 0) =
    slopeTermPos27 kv 0 13 3 1 s4 u := by
  unfold spPos27_0 slopeTermPos27
  cases kv.testBit 0
  · rfl
  · simp only [evalBits, Bool.cond_true, shiftLeft_eq_mul_pow]
    ring
theorem spNeg27_0_eq (kv u s4 : ℕ) :
    spNeg27_0 (kv.testBit 0) (cond (uRotBit u s4 13) 1 0) (cond (uRotBit u s4 14) 1 0)
      (cond (uRotBit u s4 15) 1 0) =
    slopeTermNeg27 kv 0 13 3 1 s4 u := by
  unfold spNeg27_0 slopeTermNeg27
  cases kv.testBit 0
  · simp only [evalBits, Bool.not_false, Bool.cond_true, shiftLeft_eq_mul_pow]
    ring
  · rfl
theorem spPos27_0_lin (b : Bool) (v13 v14 v15 : ℕ) :
    spPos27_0 b v13 v14 v15 =
      spPos27_0 b 1 0 0 * v13 +
      spPos27_0 b 0 1 0 * v14 +
      spPos27_0 b 0 0 1 * v15 := by
  unfold spPos27_0
  cases b <;> simp only [Bool.cond_true, Bool.cond_false] <;> ring
theorem spNeg27_0_lin (b : Bool) (v13 v14 v15 : ℕ) :
    spNeg27_0 b v13 v14 v15 =
      spNeg27_0 b 1 0 0 * v13 +
      spNeg27_0 b 0 1 0 * v14 +
      spNeg27_0 b 0 0 1 * v15 := by
  unfold spNeg27_0
  cases b <;>
    simp only [Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false] <;>
    ring
theorem spPos27_0_zero (b : Bool) : spPos27_0 b 0 0 0 = 0 := by
  unfold spPos27_0
  cases b <;> simp
theorem spNeg27_0_zero (b : Bool) : spNeg27_0 b 0 0 0 = 0 := by
  unfold spNeg27_0
  cases b <;> simp
def spPos27_1 (b : Bool) (v12 v13 v14 v15 : ℕ) : ℕ :=
  cond b ((v12 + 2 * v13 + 4 * v14 + 8 * v15) * 1) 0
def spNeg27_1 (b : Bool) (v12 v13 v14 v15 : ℕ) : ℕ :=
  cond (!b) ((v12 + 2 * v13 + 4 * v14 + 8 * v15) * 1) 0
theorem spPos27_1_eq (kv u s4 : ℕ) :
    spPos27_1 (kv.testBit 1) (cond (uRotBit u s4 12) 1 0) (cond (uRotBit u s4 13) 1 0)
      (cond (uRotBit u s4 14) 1 0) (cond (uRotBit u s4 15) 1 0) =
    slopeTermPos27 kv 1 12 4 1 s4 u := by
  unfold spPos27_1 slopeTermPos27
  cases kv.testBit 1
  · rfl
  · simp only [evalBits, Bool.cond_true, shiftLeft_eq_mul_pow]
    ring
theorem spNeg27_1_eq (kv u s4 : ℕ) :
    spNeg27_1 (kv.testBit 1) (cond (uRotBit u s4 12) 1 0) (cond (uRotBit u s4 13) 1 0)
      (cond (uRotBit u s4 14) 1 0) (cond (uRotBit u s4 15) 1 0) =
    slopeTermNeg27 kv 1 12 4 1 s4 u := by
  unfold spNeg27_1 slopeTermNeg27
  cases kv.testBit 1
  · simp only [evalBits, Bool.not_false, Bool.cond_true, shiftLeft_eq_mul_pow]
    ring
  · rfl
theorem spPos27_1_lin (b : Bool) (v12 v13 v14 v15 : ℕ) :
    spPos27_1 b v12 v13 v14 v15 =
      spPos27_1 b 1 0 0 0 * v12 +
      spPos27_1 b 0 1 0 0 * v13 +
      spPos27_1 b 0 0 1 0 * v14 +
      spPos27_1 b 0 0 0 1 * v15 := by
  unfold spPos27_1
  cases b <;> simp only [Bool.cond_true, Bool.cond_false] <;> ring
theorem spNeg27_1_lin (b : Bool) (v12 v13 v14 v15 : ℕ) :
    spNeg27_1 b v12 v13 v14 v15 =
      spNeg27_1 b 1 0 0 0 * v12 +
      spNeg27_1 b 0 1 0 0 * v13 +
      spNeg27_1 b 0 0 1 0 * v14 +
      spNeg27_1 b 0 0 0 1 * v15 := by
  unfold spNeg27_1
  cases b <;>
    simp only [Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false] <;>
    ring
theorem spPos27_1_zero (b : Bool) : spPos27_1 b 0 0 0 0 = 0 := by
  unfold spPos27_1
  cases b <;> simp
theorem spNeg27_1_zero (b : Bool) : spNeg27_1 b 0 0 0 0 = 0 := by
  unfold spNeg27_1
  cases b <;> simp
def spPos27_2 (b : Bool) (v11 v12 v13 v14 v15 : ℕ) : ℕ :=
  cond b ((v11 + 2 * v12 + 4 * v13 + 8 * v14 + 16 * v15) * 1) 0
def spNeg27_2 (b : Bool) (v11 v12 v13 v14 v15 : ℕ) : ℕ :=
  cond (!b) ((v11 + 2 * v12 + 4 * v13 + 8 * v14 + 16 * v15) * 1) 0
theorem spPos27_2_eq (kv u s4 : ℕ) :
    spPos27_2 (kv.testBit 2) (cond (uRotBit u s4 11) 1 0) (cond (uRotBit u s4 12) 1 0)
      (cond (uRotBit u s4 13) 1 0) (cond (uRotBit u s4 14) 1 0) (cond (uRotBit u s4 15) 1 0) =
    slopeTermPos27 kv 2 11 5 1 s4 u := by
  unfold spPos27_2 slopeTermPos27
  cases kv.testBit 2
  · rfl
  · simp only [evalBits, Bool.cond_true, shiftLeft_eq_mul_pow]
    ring
theorem spNeg27_2_eq (kv u s4 : ℕ) :
    spNeg27_2 (kv.testBit 2) (cond (uRotBit u s4 11) 1 0) (cond (uRotBit u s4 12) 1 0)
      (cond (uRotBit u s4 13) 1 0) (cond (uRotBit u s4 14) 1 0) (cond (uRotBit u s4 15) 1 0) =
    slopeTermNeg27 kv 2 11 5 1 s4 u := by
  unfold spNeg27_2 slopeTermNeg27
  cases kv.testBit 2
  · simp only [evalBits, Bool.not_false, Bool.cond_true, shiftLeft_eq_mul_pow]
    ring
  · rfl
theorem spPos27_2_lin (b : Bool) (v11 v12 v13 v14 v15 : ℕ) :
    spPos27_2 b v11 v12 v13 v14 v15 =
      spPos27_2 b 1 0 0 0 0 * v11 +
      spPos27_2 b 0 1 0 0 0 * v12 +
      spPos27_2 b 0 0 1 0 0 * v13 +
      spPos27_2 b 0 0 0 1 0 * v14 +
      spPos27_2 b 0 0 0 0 1 * v15 := by
  unfold spPos27_2
  cases b <;> simp only [Bool.cond_true, Bool.cond_false] <;> ring
theorem spNeg27_2_lin (b : Bool) (v11 v12 v13 v14 v15 : ℕ) :
    spNeg27_2 b v11 v12 v13 v14 v15 =
      spNeg27_2 b 1 0 0 0 0 * v11 +
      spNeg27_2 b 0 1 0 0 0 * v12 +
      spNeg27_2 b 0 0 1 0 0 * v13 +
      spNeg27_2 b 0 0 0 1 0 * v14 +
      spNeg27_2 b 0 0 0 0 1 * v15 := by
  unfold spNeg27_2
  cases b <;>
    simp only [Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false] <;>
    ring
theorem spPos27_2_zero (b : Bool) : spPos27_2 b 0 0 0 0 0 = 0 := by
  unfold spPos27_2
  cases b <;> simp
theorem spNeg27_2_zero (b : Bool) : spNeg27_2 b 0 0 0 0 0 = 0 := by
  unfold spNeg27_2
  cases b <;> simp
def spPos27_3 (b : Bool) (v10 v11 v12 v13 v14 v15 : ℕ) : ℕ :=
  cond b ((v10 + 2 * v11 + 4 * v12 + 8 * v13 + 16 * v14 + 32 * v15) * 1) 0
def spNeg27_3 (b : Bool) (v10 v11 v12 v13 v14 v15 : ℕ) : ℕ :=
  cond (!b) ((v10 + 2 * v11 + 4 * v12 + 8 * v13 + 16 * v14 + 32 * v15) * 1) 0
theorem spPos27_3_eq (kv u s4 : ℕ) :
    spPos27_3 (kv.testBit 3) (cond (uRotBit u s4 10) 1 0) (cond (uRotBit u s4 11) 1 0)
      (cond (uRotBit u s4 12) 1 0) (cond (uRotBit u s4 13) 1 0) (cond (uRotBit u s4 14) 1 0)
      (cond (uRotBit u s4 15) 1 0) =
    slopeTermPos27 kv 3 10 6 1 s4 u := by
  unfold spPos27_3 slopeTermPos27
  cases kv.testBit 3
  · rfl
  · simp only [evalBits, Bool.cond_true, shiftLeft_eq_mul_pow]
    ring
theorem spNeg27_3_eq (kv u s4 : ℕ) :
    spNeg27_3 (kv.testBit 3) (cond (uRotBit u s4 10) 1 0) (cond (uRotBit u s4 11) 1 0)
      (cond (uRotBit u s4 12) 1 0) (cond (uRotBit u s4 13) 1 0) (cond (uRotBit u s4 14) 1 0)
      (cond (uRotBit u s4 15) 1 0) =
    slopeTermNeg27 kv 3 10 6 1 s4 u := by
  unfold spNeg27_3 slopeTermNeg27
  cases kv.testBit 3
  · simp only [evalBits, Bool.not_false, Bool.cond_true, shiftLeft_eq_mul_pow]
    ring
  · rfl
theorem spPos27_3_lin (b : Bool) (v10 v11 v12 v13 v14 v15 : ℕ) :
    spPos27_3 b v10 v11 v12 v13 v14 v15 =
      spPos27_3 b 1 0 0 0 0 0 * v10 +
      spPos27_3 b 0 1 0 0 0 0 * v11 +
      spPos27_3 b 0 0 1 0 0 0 * v12 +
      spPos27_3 b 0 0 0 1 0 0 * v13 +
      spPos27_3 b 0 0 0 0 1 0 * v14 +
      spPos27_3 b 0 0 0 0 0 1 * v15 := by
  unfold spPos27_3
  cases b <;> simp only [Bool.cond_true, Bool.cond_false] <;> ring
theorem spNeg27_3_lin (b : Bool) (v10 v11 v12 v13 v14 v15 : ℕ) :
    spNeg27_3 b v10 v11 v12 v13 v14 v15 =
      spNeg27_3 b 1 0 0 0 0 0 * v10 +
      spNeg27_3 b 0 1 0 0 0 0 * v11 +
      spNeg27_3 b 0 0 1 0 0 0 * v12 +
      spNeg27_3 b 0 0 0 1 0 0 * v13 +
      spNeg27_3 b 0 0 0 0 1 0 * v14 +
      spNeg27_3 b 0 0 0 0 0 1 * v15 := by
  unfold spNeg27_3
  cases b <;>
    simp only [Bool.not_true, Bool.not_false, Bool.cond_true, Bool.cond_false] <;>
    ring
theorem spPos27_3_zero (b : Bool) : spPos27_3 b 0 0 0 0 0 0 = 0 := by
  unfold spPos27_3
  cases b <;> simp
theorem spNeg27_3_zero (b : Bool) : spNeg27_3 b 0 0 0 0 0 0 = 0 := by
  unfold spNeg27_3
  cases b <;> simp

end ArcsinImpl

end QuantumComputation.Specs
