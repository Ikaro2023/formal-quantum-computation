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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.FusedSlot4Slot0

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section SlimStageADepsB
set_option maxRecDepth 131072

section SharedScope
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
local instance (priority := 1000000) instNeZeroAlt (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open _root_.DynamicCircuit DynCircuitExt
open Circuit hiding TOFF
open PrimitiveGate (T TOFF)
open Operator QProg Matrix Real
open scoped Matrix BigOperators
namespace StageAPointPhase128OnStep
open KaratsubaQft64Matrix (omega128 omega128_add star_mul_omega128_self bitXor bit6)
open DyadicQft64Engine DyadicQft64 DyadicQft64WalkCircuit DyadicQft64WalkCircuit288
open FullSysCatSegmentBridge (fullSysCoreWires)
open CoreQftHadamard140And160 (CanonStageSpec128 nCanon4062 rQftCanon128 rWorkCanon128 rSysCanon128
  rPGCanon128 rSysCanon128_disjoint_rPGCanon128 rSysCanon128_disjoint_rWorkCanon128
  rPGCanon128_disjoint_rWorkCanon128)
open StageAPosHeadConjugatedCircuit (uCoreHadamard6)
open HeldRSum42TwistQftPass2Stitch (rAxisPrefix rAxisPrefix_disjoint
  axisProdPrefix CanonStageSpec128.ofAxisPrefixCircuit stageHPrefixCanonStage128)
open HermitianMat
open SpecsAux SpecsAux.SpecMirror
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
section ApexButterflyEngine128
variable {Var : Type} {n : ℕ}
def cnotPairsCircuit : (wpairs : List (Wire n × Wire n)) → (∀ p ∈ wpairs, p.1 ≠ p.2) → Circuit n
  | [], _ => Circuit.identity
  | p :: rest, hne =>
      Circuit.CNOT p.1 p.2 (hne p List.mem_cons_self) ;;ᶜ
        cnotPairsCircuit rest (fun q hq ↦ hne q (List.mem_cons_of_mem p hq))
@[simp] theorem count_cnotPairsCircuit_toff :
    ∀ (wpairs : List (Wire n × Wire n)) (hne : ∀ p ∈ wpairs, p.1 ≠ p.2),
      (cnotPairsCircuit wpairs hne).count TOFF = 0
  | [], _ => by simp [cnotPairsCircuit]
  | _ :: rest, hne => by simp [cnotPairsCircuit, count_cnotPairsCircuit_toff rest]
@[simp] theorem count_cnotPairsCircuit_t :
    ∀ (wpairs : List (Wire n × Wire n)) (hne : ∀ p ∈ wpairs, p.1 ≠ p.2),
      (cnotPairsCircuit wpairs hne).count .T = 0
  | [], _ => by simp [cnotPairsCircuit]
  | _ :: rest, hne => by simp [cnotPairsCircuit, count_cnotPairsCircuit_t rest]
def cnotPairsPerm : List (Wire n × Wire n) → BitAssignment n → BitAssignment n
  | [], β => β
  | p :: rest, β => cnotPairsPerm rest (Function.update β p.2 (β p.2 + β p.1))
theorem cnotPairsPerm_append :
    ∀ (A B : List (Wire n × Wire n)) (β : BitAssignment n),
      cnotPairsPerm (A ++ B) β = cnotPairsPerm B (cnotPairsPerm A β)
  | [], _, _ => rfl
  | p :: rest, B, β => cnotPairsPerm_append rest B (Function.update β p.2 (β p.2 + β p.1))
theorem cnotPairsPerm_outside :
    ∀ (wpairs : List (Wire n × Wire n)) (β : BitAssignment n) (w : Wire n),
      (∀ p ∈ wpairs, p.2 ≠ w) → cnotPairsPerm wpairs β w = β w
  | [], _, _, _ => rfl
  | p :: rest, β, w, hout => by
      dsimp only [cnotPairsPerm]
      rw [cnotPairsPerm_outside rest _ w (fun q hq ↦ hout q (List.mem_cons_of_mem p hq)),
        Function.update_of_ne (hout p List.mem_cons_self).symm]
theorem cnotPairsPerm_eq_on_superset {S : Finset (Wire n)} :
    ∀ (wpairs : List (Wire n × Wire n)),
      (∀ p ∈ wpairs, p.1 ∈ S ∧ p.2 ∈ S) →
      ∀ {β₁ β₂ : BitAssignment n},
        (∀ w ∈ S, β₁ w = β₂ w) →
        ∀ w ∈ S, cnotPairsPerm wpairs β₁ w = cnotPairsPerm wpairs β₂ w
  | [], _, _, _, hEq, w, hw => hEq w hw
  | p :: rest, hS, β₁, β₂, hEq, w, hw => by
      have hp := hS p List.mem_cons_self
      refine cnotPairsPerm_eq_on_superset rest (fun q hq ↦ hS q (List.mem_cons_of_mem p hq))
        (fun u hu ↦ ?_) w hw
      by_cases hu2 : u = p.2
      · subst hu2
        rw [Function.update_self, Function.update_self, hEq p.2 hp.2, hEq p.1 hp.1]
      · rw [Function.update_of_ne hu2, Function.update_of_ne hu2, hEq u hu]
theorem cnotStep_involutive {c t : Wire n} (hne : c ≠ t) (β : BitAssignment n) :
    let β' := Function.update β t (β t + β c)
    Function.update β' t (β' t + β' c) = β := by
  intro β'
  funext w
  by_cases hw : w = t
  · subst hw
    dsimp only [β']
    rw [Function.update_self, Function.update_self, Function.update_of_ne hne,
      zmod2_add_cancel_right]
  · dsimp only [β']
    rw [Function.update_of_ne hw, Function.update_of_ne hw]
theorem cnotPairsPerm_reverse_cancel :
    ∀ (wpairs : List (Wire n × Wire n)),
      (∀ p ∈ wpairs, p.1 ≠ p.2) →
      ∀ (β : BitAssignment n),
        cnotPairsPerm wpairs.reverse (cnotPairsPerm wpairs β) = β
  | [], _, _ => rfl
  | p :: rest, hne, β => by
      simp only [List.reverse_cons, cnotPairsPerm]
      rw [cnotPairsPerm_append,
        cnotPairsPerm_reverse_cancel rest (fun q hq ↦ hne q (List.mem_cons_of_mem p hq))]
      exact cnotStep_involutive (hne p List.mem_cons_self) β
theorem classicalPerm_cnotPairsCircuit :
    ∀ (wpairs : List (Wire n × Wire n)) (hne : ∀ p ∈ wpairs, p.1 ≠ p.2),
      ClassicalPerm (cnotPairsCircuit wpairs hne) (cnotPairsPerm wpairs)
  | [], _ => ClassicalPerm.identity
  | p :: rest, hne =>
      (ClassicalPerm.CNOT p.1 p.2 (hne p List.mem_cons_self)).seq
        (classicalPerm_cnotPairsCircuit rest (fun q hq ↦ hne q (List.mem_cons_of_mem p hq)))
def localPerm6 : List (Fin 6 × Fin 6) → (Fin 6 → ZMod 2) → (Fin 6 → ZMod 2)
  | [], b => b
  | p :: rest, b => localPerm6 rest (Function.update b p.2 (b p.2 + b p.1))
def axisCnotPairs {kSys : ℕ} (rSys : QRegister kSys n)
    (g : Fin 6 → Fin kSys) (pairs6 : List (Fin 6 × Fin 6)) : List (Wire n × Wire n) :=
  pairs6.map fun p ↦ (rSys (g p.1), rSys (g p.2))
def batchCnotPairs {kSys : ℕ} (rSys : QRegister kSys n) (pairs6 : List (Fin 6 × Fin 6)) :
    ∀ {L : ℕ}, (Fin L → Fin 6 → Fin kSys) → List (Wire n × Wire n)
  | 0, _ => []
  | _ + 1, idxAx =>
      axisCnotPairs rSys (idxAx 0) pairs6 ++
        batchCnotPairs rSys pairs6 (fun l ↦ idxAx l.succ)
theorem batchCnotPairs_hne {kSys : ℕ} (rSys : QRegister kSys n)
    (pairs6 : List (Fin 6 × Fin 6)) (hne6 : ∀ p ∈ pairs6, p.1 ≠ p.2) :
    ∀ {L : ℕ} (idxAx : Fin L → Fin 6 → Fin kSys),
      Function.Injective (fun p : Fin L × Fin 6 ↦ idxAx p.1 p.2) →
      ∀ wp ∈ batchCnotPairs rSys pairs6 idxAx, wp.1 ≠ wp.2
  | 0, _, _, _, hmem => by simp [batchCnotPairs] at hmem
  | _ + 1, idxAx, hinj, wp, hmem => by
      rcases List.mem_append.mp hmem with hhead | htail
      · rcases List.mem_map.mp hhead with ⟨p, hp, rfl⟩
        intro heq
        have hp_eq : ((0, p.1) : Fin _ × Fin 6) = (0, p.2) := hinj (rSys.wires.injective heq)
        exact hne6 p hp (congrArg Prod.snd hp_eq)
      · exact batchCnotPairs_hne rSys pairs6 hne6 (fun l ↦ idxAx l.succ)
          (by
            rintro ⟨a1, a2⟩ ⟨b1, b2⟩ h
            have hab : ((a1.succ, a2) : Fin _ × Fin 6) = (b1.succ, b2) := hinj h
            have h1 : a1.succ = b1.succ := congrArg Prod.fst hab
            have h2 : a2 = b2 := congrArg Prod.snd hab
            exact Prod.ext (Fin.succ_injective _ h1) h2)
          wp htail
theorem batchCnotPairs_mem_sys {kSys : ℕ} (rSys : QRegister kSys n)
    (pairs6 : List (Fin 6 × Fin 6)) :
    ∀ {L : ℕ} (idxAx : Fin L → Fin 6 → Fin kSys)
      (wp : Wire n × Wire n), wp ∈ batchCnotPairs rSys pairs6 idxAx →
      wp.1 ∈ rSys.image ∧ wp.2 ∈ rSys.image
  | 0, _, _, hmem => by simp [batchCnotPairs] at hmem
  | _ + 1, idxAx, wp, hmem => by
      rcases List.mem_append.mp hmem with hhead | htail
      · rcases List.mem_map.mp hhead with ⟨p, _, rfl⟩
        exact ⟨(QRegister.mem_image rSys _).mpr ⟨_, rfl⟩,
          (QRegister.mem_image rSys _).mpr ⟨_, rfl⟩⟩
      · exact batchCnotPairs_mem_sys rSys pairs6 (fun l ↦ idxAx l.succ) wp htail
theorem cnotPairsPerm_axis_outside {kSys : ℕ} (rSys : QRegister kSys n)
    (g : Fin 6 → Fin kSys) (pairs6 : List (Fin 6 × Fin 6))
    (δ : BitAssignment n) (w : Wire n) (hout : ∀ q : Fin 6, rSys (g q) ≠ w) :
    cnotPairsPerm (axisCnotPairs rSys g pairs6) δ w = δ w :=
  cnotPairsPerm_outside _ δ w fun wp hwp ↦ by
    rcases List.mem_map.mp hwp with ⟨p, _, rfl⟩
    exact hout p.2
theorem cnotPairsPerm_axis_apply {kSys : ℕ} (rSys : QRegister kSys n)
    (g : Fin 6 → Fin kSys) (hinj : Function.Injective g) :
    ∀ (pairs6 : List (Fin 6 × Fin 6)) (δ : BitAssignment n) (q : Fin 6),
      cnotPairsPerm (axisCnotPairs rSys g pairs6) δ (rSys (g q)) =
        localPerm6 pairs6 (fun i ↦ δ (rSys (g i))) q
  | [], _, _ => rfl
  | p :: rest, δ, q => by
      dsimp only [axisCnotPairs, List.map, cnotPairsPerm, localPerm6]
      change cnotPairsPerm (axisCnotPairs rSys g rest) _ _ = _
      rw [cnotPairsPerm_axis_apply rSys g hinj rest]
      congr 1; funext i
      by_cases hi : i = p.2
      · subst hi; simp [Function.update_self]
      · have hne_w : rSys (g i) ≠ rSys (g p.2) := fun h ↦ hi (hinj (rSys.wires.injective h))
        simp [Function.update_of_ne hi, Function.update_of_ne hne_w]
theorem cnotPairsPerm_batch_outside {kSys : ℕ} (rSys : QRegister kSys n)
    (pairs6 : List (Fin 6 × Fin 6)) :
    ∀ {L : ℕ} (idxAx : Fin L → Fin 6 → Fin kSys) (δ : BitAssignment n) (w : Wire n),
      (∀ (l : Fin L) (q : Fin 6), rSys (idxAx l q) ≠ w) →
      cnotPairsPerm (batchCnotPairs rSys pairs6 idxAx) δ w = δ w
  | 0, _, _, _, _ => rfl
  | _ + 1, idxAx, δ, w, hout => by
      rw [batchCnotPairs, cnotPairsPerm_append,
        cnotPairsPerm_batch_outside rSys pairs6 (fun l ↦ idxAx l.succ) _ w
          (fun l q ↦ hout l.succ q),
        cnotPairsPerm_axis_outside rSys (idxAx 0) pairs6 δ w (fun q ↦ hout 0 q)]
theorem cnotPairsPerm_batch_apply {kSys : ℕ} (rSys : QRegister kSys n)
    (pairs6 : List (Fin 6 × Fin 6)) :
    ∀ {L : ℕ} (idxAx : Fin L → Fin 6 → Fin kSys),
      Function.Injective (fun p : Fin L × Fin 6 ↦ idxAx p.1 p.2) →
      ∀ (δ : BitAssignment n) (l : Fin L) (q : Fin 6),
        cnotPairsPerm (batchCnotPairs rSys pairs6 idxAx) δ (rSys (idxAx l q)) =
          localPerm6 pairs6 (fun i ↦ δ (rSys (idxAx l i))) q
  | 0, _, _, _, l, _ => Fin.elim0 l
  | _ + 1, idxAx, hinj, δ, l, q => by
      rw [batchCnotPairs, cnotPairsPerm_append]
      let δ₁ := cnotPairsPerm (axisCnotPairs rSys (idxAx 0) pairs6) δ
      have hinj0 : Function.Injective (idxAx 0) := fun a b h ↦
        have hp : ((0, a) : Fin _ × Fin 6) = (0, b) := hinj h
        congrArg Prod.snd hp
      have hinj_succ : Function.Injective (fun p : Fin _ × Fin 6 ↦ idxAx p.1.succ p.2) := by
        rintro ⟨a1, a2⟩ ⟨b1, b2⟩ h
        have hab : ((a1.succ, a2) : Fin _ × Fin 6) = (b1.succ, b2) := hinj h
        have h1 : a1.succ = b1.succ := congrArg Prod.fst hab
        have h2 : a2 = b2 := congrArg Prod.snd hab
        exact Prod.ext (Fin.succ_injective _ h1) h2
      refine Fin.cases ?_ (fun l' ↦ ?_) l
      · rw [cnotPairsPerm_batch_outside rSys pairs6 (fun m ↦ idxAx m.succ) δ₁ (rSys (idxAx 0 q))
          (fun m r heq ↦
            have hp : ((m.succ, r) : Fin _ × Fin 6) = (0, q) := hinj (rSys.wires.injective heq)
            Fin.succ_ne_zero m (congrArg Prod.fst hp))]
        exact cnotPairsPerm_axis_apply rSys (idxAx 0) hinj0 pairs6 δ q
      · rw [cnotPairsPerm_batch_apply rSys pairs6 (fun m ↦ idxAx m.succ) hinj_succ δ₁ l' q]
        congr 1; funext i
        exact cnotPairsPerm_axis_outside rSys (idxAx 0) pairs6 δ (rSys (idxAx l'.succ i))
          (fun r heq ↦
            have hp : ((l'.succ, i) : Fin _ × Fin 6) = (0, r) := hinj (rSys.wires.injective
                heq.symm)
            Fin.succ_ne_zero l' (congrArg Prod.fst hp))
structure ForestSlotConfig (s : ℕ) where
  pairs : List (Fin 6 × Fin 6)
  hne : ∀ p ∈ pairs, p.1 ≠ p.2
  qCin0 : Fin 6
  col0Tail6 : List (Fin 6)
  colRest6 : Fin (3 - s) → List (Fin 6)
  hCinNotTail : qCin0 ∉ col0Tail6
  hTailNodup : col0Tail6.Nodup
  hRestNodup : ∀ r : Fin (3 - s), (colRest6 r).Nodup
  hCinDisjRest : ∀ (r : Fin (3 - s)), qCin0 ∉ colRest6 r
  hTailDisjRest : ∀ (r : Fin (3 - s)) (q : Fin 6), q ∈ col0Tail6 → q ∉ colRest6 r
  hRestDisj : ∀ (r₁ r₂ : Fin (3 - s)), r₁ ≠ r₂ → ∀ q ∈ colRest6 r₁, q ∉ colRest6 r₂
def xorForestBucketsLen (s : ℕ) (cfg : ForestSlotConfig s) (L : ℕ) : List ℕ :=
  ((L - 1) + cfg.col0Tail6.length * L) :: (List.ofFn fun r : Fin (3 - s) ↦ (cfg.colRest6 r).length
      * L)
def xorForestBatchWork (s : ℕ) (cfg : ForestSlotConfig s) (L : ℕ) : ℕ :=
  1 + compressStepsNat (xorForestBucketsLen s cfg L) 0 + (4 - s)
def xorForestBatchTCost (s : ℕ) (cfg : ForestSlotConfig s) (L : ℕ) : ℕ := 4 * compressStepsNat
    (xorForestBucketsLen s cfg L) 0 + finalCarriesNat (xorForestBucketsLen s cfg L) 0 +
    (4 * (4 - s) + 1)
def forestAxisNat (s : ℕ) (cfg : ForestSlotConfig s) (b : Fin 6 → ZMod 2) : ℕ := 2 ^ s *
    ((localPerm6 cfg.pairs b cfg.qCin0).val + (cfg.col0Tail6.map fun q ↦ (localPerm6 cfg.pairs
    b q).val).sum) + ∑ r : Fin (3 - s), 2 ^ (s + (r.val + 1)) *
    ((cfg.colRest6 r).map fun q ↦ (localPerm6 cfg.pairs b q).val).sum
def expandColWires {L kSys : ℕ} (rSys : QRegister kSys n)
    (idxAx : Fin L → Fin 6 → Fin kSys) : List (Fin 6) → List (Wire n)
  | [] => []
  | q :: qs => finMapList (fun l : Fin L ↦ rSys (idxAx l q)) ++ expandColWires rSys idxAx qs
theorem expandColWires_length {L kSys : ℕ} (rSys : QRegister kSys n)
    (idxAx : Fin L → Fin 6 → Fin kSys) :
    ∀ (qs : List (Fin 6)), (expandColWires rSys idxAx qs).length = qs.length * L
  | [] => by simp [expandColWires]
  | q :: qs => by
      simp only [expandColWires, List.length_append, finMapList_length,
        expandColWires_length rSys idxAx qs, List.length_cons]
      ring
theorem finMapList_map_length_eq_ofFn {α : Type*} :
    ∀ {m : ℕ} (g : Fin m → List α),
      (finMapList g).map List.length = List.ofFn (fun r : Fin m ↦ (g r).length)
  | 0, _ => by
      have h0 : finMapList (L := 0) = fun (_ : Fin 0 → List α) ↦ ([] : List (List α)) := by
        funext f; exact List.eq_nil_of_length_eq_zero (finMapList_length f)
      simp [h0]
  | m + 1, g => by
      have hcons : finMapList g = g 0 :: finMapList (fun r : Fin m ↦ g r.succ) := by
        conv_lhs => unfold finMapList
      rw [hcons, List.map_cons, finMapList_map_length_eq_ofFn (fun r ↦ g r.succ), List.ofFn_succ]
theorem mem_expandColWires {L kSys : ℕ} (rSys : QRegister kSys n)
    (idxAx : Fin L → Fin 6 → Fin kSys) :
    ∀ (qs : List (Fin 6)) (w : Wire n),
      w ∈ expandColWires rSys idxAx qs ↔ ∃ q ∈ qs, ∃ l : Fin L, rSys (idxAx l q) = w
  | [], w => by simp [expandColWires]
  | q :: qs, w => by
      simp only [expandColWires, List.mem_append, mem_finMapList,
        mem_expandColWires rSys idxAx qs, List.mem_cons]
      constructor
      · rintro (⟨l, rfl⟩ | ⟨q', hq', l, rfl⟩)
        · exact ⟨q, Or.inl rfl, l, rfl⟩
        · exact ⟨q', Or.inr hq', l, rfl⟩
      · rintro ⟨q', rfl | hq', l, rfl⟩
        · exact Or.inl ⟨l, rfl⟩
        · exact Or.inr ⟨q', hq', l, rfl⟩
theorem expandColWires_nodup {L kSys : ℕ} (rSys : QRegister kSys n)
    (idxAx : Fin L → Fin 6 → Fin kSys)
    (hinj : Function.Injective (fun p : Fin L × Fin 6 ↦ idxAx p.1 p.2)) :
    ∀ (qs : List (Fin 6)), qs.Nodup → (expandColWires rSys idxAx qs).Nodup
  | [], _ => List.nodup_nil
  | q :: qs, hnd => by
      obtain ⟨hq_not, hqs_nd⟩ := List.nodup_cons.mp hnd
      rw [expandColWires, List.nodup_append]
      refine ⟨finMapList_nodup (fun l₁ l₂ h ↦
          have hp : ((l₁, q) : Fin L × Fin 6) = (l₂, q) := hinj (rSys.wires.injective h)
          congrArg Prod.fst hp),
        expandColWires_nodup rSys idxAx hinj qs hqs_nd,
        fun x hx y hy hxy ↦ ?_⟩
      subst hxy
      rcases mem_finMapList.mp hx with ⟨l₁, rfl⟩
      rcases (mem_expandColWires rSys idxAx qs _).mp hy with ⟨q', hq', l₂, heq⟩
      have hp : ((l₂, q') : Fin L × Fin 6) = (l₁, q) := hinj (rSys.wires.injective heq)
      have hq_eq : q' = q := congrArg Prod.snd hp
      exact hq_not (hq_eq ▸ hq')
theorem wireListSum_expandColWires {L kSys : ℕ} (rSys : QRegister kSys n)
    (idxAx : Fin L → Fin 6 → Fin kSys) (δ : BitAssignment n) :
    ∀ (qs : List (Fin 6)),
      wireListSum (expandColWires rSys idxAx qs) δ =
        ∑ l : Fin L, (qs.map fun q ↦ (δ (rSys (idxAx l q))).val).sum
  | [] => by simp [expandColWires]
  | q :: qs => by
      rw [expandColWires, wireListSum_append, wireListSum_finMapList,
        wireListSum_expandColWires rSys idxAx δ qs, ← Finset.sum_add_distrib]
      rfl
theorem weightedBuckets_forest_eq {L kSys : ℕ} (s : ℕ) (cfg : ForestSlotConfig s)
    (hL : 1 ≤ L) (rSys : QRegister kSys n) (idxAx : Fin L → Fin 6 → Fin kSys)
    (hinj : Function.Injective (fun p : Fin L × Fin 6 ↦ idxAx p.1 p.2))
    (γ : BitAssignment kSys) :
    let β₁ := cnotPairsPerm (batchCnotPairs rSys cfg.pairs idxAx) (canonAssign rSys γ)
    let wCin0 : Wire n := rSys (idxAx ⟨0, hL⟩ cfg.qCin0)
    let col0Bucket : List (Wire n) :=
      finMapList (fun i : Fin (L - 1) ↦ rSys (idxAx ⟨i.val + 1, by omega⟩ cfg.qCin0)) ++
        expandColWires rSys idxAx cfg.col0Tail6
    let colRest : Fin (3 - s) → List (Wire n) :=
      fun r ↦ expandColWires rSys idxAx (cfg.colRest6 r)
    2 ^ s * ((β₁ wCin0).val + weightedBucketsVal (col0Bucket :: finMapList colRest) β₁) =
      ∑ l : Fin L, forestAxisNat s cfg (fun i ↦ γ (idxAx l i)) := by
  intro β₁ wCin0 col0Bucket colRest
  have hβ₁ : ∀ (l : Fin L) (q : Fin 6),
      β₁ (rSys (idxAx l q)) = localPerm6 cfg.pairs (fun i ↦ γ (idxAx l i)) q := by
    intro l q
    dsimp only [β₁]
    rw [cnotPairsPerm_batch_apply rSys cfg.pairs idxAx hinj]
    congr 1; funext i
    exact canonAssign_apply_sys rSys γ (idxAx l i)
  rw [weightedBucketsVal]
  have hcol0 : (β₁ wCin0).val + wireListSum col0Bucket β₁ = ∑ l : Fin L, ((β₁ (rSys (idxAx l
      cfg.qCin0))).val + (cfg.col0Tail6.map fun q ↦ (β₁ (rSys (idxAx l q))).val).sum) := by
    dsimp only [wCin0, col0Bucket]
    rw [wireListSum_append, ← add_assoc,
      head_add_wireListSum_tail hL (fun l : Fin L ↦ rSys (idxAx l cfg.qCin0)) β₁,
      wireListSum_expandColWires, ← Finset.sum_add_distrib]
  rw [← add_assoc, hcol0, weightedBucketsVal_finMapList]
  simp only [colRest, wireListSum_expandColWires]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  have hswap : (∑ r : Fin (3 - s), 2 ^ s * (2 * (2 ^ r.val * ∑ l : Fin L, ((cfg.colRest6
      r).map fun q ↦ (β₁ (rSys (idxAx l q))).val).sum))) = ∑ l : Fin L, ∑ r : Fin (3 - s), 2 ^
      (s + (r.val + 1)) * ((cfg.colRest6 r).map fun q ↦ (β₁ (rSys (idxAx l q))).val).sum := by
    have h1 : ∀ r : Fin (3 - s),
        2 ^ s * (2 * (2 ^ r.val * ∑ l : Fin L,
            ((cfg.colRest6 r).map fun q ↦ (β₁ (rSys (idxAx l q))).val).sum)) =
          ∑ l : Fin L, 2 ^ (s + (r.val + 1)) *
            ((cfg.colRest6 r).map fun q ↦ (β₁ (rSys (idxAx l q))).val).sum := fun r ↦ by
      have hp : 2 ^ (s + (r.val + 1)) = 2 ^ s * (2 * 2 ^ r.val) := by
        rw [Nat.add_comm (r.val) 1, ← Nat.add_assoc, pow_add, pow_add, pow_one]; ring
      rw [hp, ← Finset.mul_sum]; ring
    simp_rw [h1]
    exact Finset.sum_comm
  rw [hswap, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  dsimp only [forestAxisNat]
  simp_rw [hβ₁ l]
def xorForestBuckets {kSys : ℕ} (s : ℕ) (cfg : ForestSlotConfig s) (L : ℕ) (hL : 1 ≤ L)
    (rSys : QRegister kSys n) (idxAx : Fin L → Fin 6 → Fin kSys) : List (List (Wire n)) :=
  (finMapList (fun i : Fin (L - 1) ↦ rSys (idxAx ⟨i.val + 1, by omega⟩ cfg.qCin0)) ++
      expandColWires rSys idxAx cfg.col0Tail6) ::
    finMapList (fun r ↦ expandColWires rSys idxAx (cfg.colRest6 r))

theorem xorForestBuckets_map_len {kSys : ℕ} (s : ℕ) (cfg : ForestSlotConfig s) (L : ℕ) (hL : 1 ≤ L)
    (rSys : QRegister kSys n) (idxAx : Fin L → Fin 6 → Fin kSys) :
    (xorForestBuckets s cfg L hL rSys idxAx).map List.length = xorForestBucketsLen s cfg L := by
  simp only [xorForestBuckets, xorForestBucketsLen, List.map_cons, List.length_append,
    finMapList_length, finMapList_map_length_eq_ofFn, expandColWires_length]

theorem xorForestBuckets_nodup {kSys : ℕ} (s : ℕ) (cfg : ForestSlotConfig s) (L : ℕ) (hL : 1 ≤ L)
    (rSys : QRegister kSys n) (idxAx : Fin L → Fin 6 → Fin kSys)
    (hinj_ax : Function.Injective (fun p : Fin L × Fin 6 ↦ idxAx p.1 p.2)) :
    ∀ B ∈ xorForestBuckets s cfg L hL rSys idxAx, B.Nodup := fun B hB ↦ by
  rcases List.mem_cons.mp hB with rfl | hB_rest
  · rw [List.nodup_append]
    refine ⟨finMapList_nodup (fun i₁ i₂ h ↦ by
        have hp : ((⟨i₁.val + 1, by omega⟩, cfg.qCin0) : Fin L × Fin 6) =
            (⟨i₂.val + 1, by omega⟩, cfg.qCin0) := hinj_ax (rSys.wires.injective h)
        have hv : i₁.val + 1 = i₂.val + 1 := congrArg (fun p : Fin L × Fin 6 ↦ p.1.val) hp
        exact Fin.ext (by omega)),
      expandColWires_nodup rSys idxAx hinj_ax cfg.col0Tail6 cfg.hTailNodup,
      fun x hx y hy hxy ↦ ?_⟩
    subst hxy
    rcases mem_finMapList.mp hx with ⟨i, rfl⟩
    rcases (mem_expandColWires rSys idxAx cfg.col0Tail6 _).mp hy with ⟨q', hq', l, heq⟩
    have hp : ((l, q') : Fin L × Fin 6) = (⟨i.val + 1, by omega⟩, cfg.qCin0) :=
      hinj_ax (rSys.wires.injective heq)
    exact cfg.hCinNotTail ((show q' = cfg.qCin0 from congrArg Prod.snd hp) ▸ hq')
  · rcases mem_finMapList.mp hB_rest with ⟨r, rfl⟩
    exact expandColWires_nodup rSys idxAx hinj_ax (cfg.colRest6 r) (cfg.hRestNodup r)

theorem xorForestBuckets_disj {kSys : ℕ} (s : ℕ) (cfg : ForestSlotConfig s) (L : ℕ) (hL : 1 ≤ L)
    (rSys : QRegister kSys n) (idxAx : Fin L → Fin 6 → Fin kSys)
    (hinj_ax : Function.Injective (fun p : Fin L × Fin 6 ↦ idxAx p.1 p.2)) :
    (xorForestBuckets s cfg L hL rSys idxAx).Pairwise fun B₁ B₂ ↦ ∀ x ∈ B₁, x ∉ B₂ := by
  rw [xorForestBuckets, List.pairwise_cons]
  refine ⟨fun B₂ hB₂ x hx₁ hx₂ ↦ ?_,
    buckets_pairwise_finMapList _ fun r₁ r₂ hne x hx₁ hx₂ ↦ ?_⟩
  · rcases mem_finMapList.mp hB₂ with ⟨r, rfl⟩
    rcases (mem_expandColWires rSys idxAx (cfg.colRest6 r) x).mp hx₂ with ⟨q₂, hq₂, l₂, rfl⟩
    rcases List.mem_append.mp hx₁ with hx_cin | hx_tail
    · rcases mem_finMapList.mp hx_cin with ⟨i, heq⟩
      have hp : ((⟨i.val + 1, by omega⟩, cfg.qCin0) : Fin L × Fin 6) = (l₂, q₂) :=
        hinj_ax (rSys.wires.injective heq)
      exact cfg.hCinDisjRest r ((show q₂ = cfg.qCin0 from (congrArg Prod.snd hp).symm) ▸ hq₂)
    · rcases (mem_expandColWires rSys idxAx cfg.col0Tail6 _).mp hx_tail with ⟨q₁, hq₁, l₁, heq⟩
      have hp : ((l₁, q₁) : Fin L × Fin 6) = (l₂, q₂) := hinj_ax (rSys.wires.injective heq)
      exact cfg.hTailDisjRest r q₁ hq₁ ((show q₂ = q₁ from (congrArg Prod.snd hp).symm) ▸ hq₂)
  · rcases (mem_expandColWires rSys idxAx (cfg.colRest6 r₁) x).mp hx₁ with ⟨q₁, hq₁, l₁, rfl⟩
    rcases (mem_expandColWires rSys idxAx (cfg.colRest6 r₂) _).mp hx₂ with ⟨q₂, hq₂, l₂, heq⟩
    have hp : ((l₂, q₂) : Fin L × Fin 6) = (l₁, q₁) := hinj_ax (rSys.wires.injective heq)
    exact cfg.hRestDisj r₁ r₂ hne q₁ hq₁ ((show q₂ = q₁ from congrArg Prod.snd hp) ▸ hq₂)

theorem xorForestBuckets_sys {kSys : ℕ} (s : ℕ) (cfg : ForestSlotConfig s) (L : ℕ) (hL : 1 ≤ L)
    (rSys : QRegister kSys n) (idxAx : Fin L → Fin 6 → Fin kSys) :
    ∀ B ∈ xorForestBuckets s cfg L hL rSys idxAx, ∀ x ∈ B, x ∈ rSys.image := fun B hB x hx ↦ by
  rcases List.mem_cons.mp hB with rfl | hB_rest
  · rcases List.mem_append.mp hx with hx_cin | hx_tail
    · rcases mem_finMapList.mp hx_cin with ⟨_, rfl⟩
      exact (QRegister.mem_image rSys _).mpr ⟨_, rfl⟩
    · rcases (mem_expandColWires rSys idxAx cfg.col0Tail6 x).mp hx_tail with ⟨_, _, _, rfl⟩
      exact (QRegister.mem_image rSys _).mpr ⟨_, rfl⟩
  · rcases mem_finMapList.mp hB_rest with ⟨r, rfl⟩
    rcases (mem_expandColWires rSys idxAx (cfg.colRest6 r) x).mp hx with ⟨_, _, _, rfl⟩
    exact (QRegister.mem_image rSys _).mpr ⟨_, rfl⟩

theorem xorForestBuckets_wcin_not_mem {kSys : ℕ} (s : ℕ) (cfg : ForestSlotConfig s) (L : ℕ) (hL : 1
    ≤ L)
    (rSys : QRegister kSys n) (idxAx : Fin L → Fin 6 → Fin kSys)
    (hinj_ax : Function.Injective (fun p : Fin L × Fin 6 ↦ idxAx p.1 p.2)) :
    ∀ B ∈ xorForestBuckets s cfg L hL rSys idxAx, rSys (idxAx ⟨0, hL⟩ cfg.qCin0) ∉ B :=
    fun B hB hmem ↦ by
  rcases List.mem_cons.mp hB with rfl | hB_rest
  · rcases List.mem_append.mp hmem with hcin | htail
    · rcases mem_finMapList.mp hcin with ⟨i, heq⟩
      have hp : ((⟨i.val + 1, by omega⟩, cfg.qCin0) : Fin L × Fin 6) = (⟨0, hL⟩, cfg.qCin0) :=
        hinj_ax (rSys.wires.injective heq)
      have hv : i.val + 1 = 0 := congrArg (fun p : Fin L × Fin 6 ↦ p.1.val) hp
      omega
    · rcases (mem_expandColWires rSys idxAx cfg.col0Tail6 _).mp htail with ⟨q', hq', l, heq⟩
      have hp : ((l, q') : Fin L × Fin 6) = (⟨0, hL⟩, cfg.qCin0) :=
        hinj_ax (rSys.wires.injective heq)
      exact cfg.hCinNotTail ((show q' = cfg.qCin0 from congrArg Prod.snd hp) ▸ hq')
  · rcases mem_finMapList.mp hB_rest with ⟨r, rfl⟩
    rcases (mem_expandColWires rSys idxAx (cfg.colRest6 r) _).mp hmem with ⟨q', hq', l, heq⟩
    have hp : ((l, q') : Fin L × Fin 6) = (⟨0, hL⟩, cfg.qCin0) :=
      hinj_ax (rSys.wires.injective heq)
    exact cfg.hCinDisjRest r ((show q' = cfg.qCin0 from congrArg Prod.snd hp) ▸ hq')

def xorForestBatchDyn (inv : Bool) {kSys mWork : ℕ} (v : Var) (s : ℕ)
    (cfg : ForestSlotConfig s) (L : ℕ) (hs : s ≤ 3) (hL : 1 ≤ L)
    (hm : xorForestBatchWork s cfg L ≤ mWork) (rSys : QRegister kSys n) (rPG : QRegister 7 n)
    (rWork : QRegister mWork n) (hdisj_SP : rSys.DisjointWires rPG)
    (hdisj_SW : rSys.DisjointWires rWork) (hdisj_PW : rPG.DisjointWires rWork)
    (idxAx : Fin L → Fin 6 → Fin kSys) (hinj_ax : Function.Injective (fun p : Fin L × Fin 6 ↦
    idxAx p.1 p.2)) : DynamicCircuit Var n :=
  let wpairs := batchCnotPairs rSys cfg.pairs idxAx
  have hne_fwd : ∀ wp ∈ wpairs, wp.1 ≠ wp.2 := batchCnotPairs_hne rSys cfg.pairs cfg.hne idxAx
      hinj_ax
  have hne_inv : ∀ wp ∈ wpairs.reverse, wp.1 ≠ wp.2 := fun wp hwp ↦ hne_fwd wp (List.mem_reverse.mp
      hwp)
  let c_xor_fwd : Circuit n := cnotPairsCircuit wpairs hne_fwd
  let c_xor_inv : Circuit n := cnotPairsCircuit wpairs.reverse hne_inv
  let buckets := xorForestBuckets s cfg L hL rSys idxAx
  have hsteps_eq : compressStepsCount buckets 0 = compressStepsNat (xorForestBucketsLen s cfg L) 0
      := by
    rw [compressStepsCount_eq_nat, xorForestBuckets_map_len]
  have hfit_csa : 0 + compressStepsCount buckets 0 ≤ mWork := by
    dsimp only [xorForestBatchWork] at hm
    rw [hsteps_eq]
    omega
  have hB_nodup := xorForestBuckets_nodup s cfg L hL rSys idxAx hinj_ax
  have hB_disj := xorForestBuckets_disj s cfg L hL rSys idxAx hinj_ax
  have hB_sys := xorForestBuckets_sys s cfg L hL rSys idxAx
  have hB_anc : ∀ B ∈ buckets, ∀ x ∈ B, x ∉ rWork.image := fun B hB x hx hm_w ↦ by
    rcases (QRegister.mem_image rSys x).mp (hB_sys B hB x hx) with ⟨i, rfl⟩
    rcases (QRegister.mem_image rWork _).mp hm_w with ⟨k, hk⟩
    exact hdisj_SW.ne i k hk.symm
  have hB_PG : ∀ B ∈ buckets, ∀ x ∈ B, x ∉ rPG.image := fun B hB x hx hm_pg ↦ by
    rcases (QRegister.mem_image rSys x).mp (hB_sys B hB x hx) with ⟨i, rfl⟩
    rcases (QRegister.mem_image rPG _).mp hm_pg with ⟨k, hk⟩
    exact hdisj_SP.ne i k hk.symm
  let out := compressBuckets rWork buckets 0 hfit_csa hB_nodup hB_disj hB_anc
  have hspec := compressBuckets_spec rPG.image rWork
    (disjWires_image (QRegExt.disjointWires_symm hdisj_PW)) buckets 0 hfit_csa hB_nodup hB_disj
      hB_anc hB_PG
  let st := out.steps.length
  have _hst : st = compressStepsNat (xorForestBucketsLen s cfg L) 0 := hspec.2.1.trans hsteps_eq
  have _hm' : 1 + st + (4 - s) ≤ mWork := by
    dsimp only [xorForestBatchWork] at hm
    omega
  let rGid : QRegister (4 - s) n := rWork.slice (0 + st) (4 - s) (by omega)
  let wZero : Wire n := rWork ⟨st + (4 - s), by omega⟩
  have hsw_len : out.sumWires.length = 4 - s := by
    rw [hspec.1]
    simp only [buckets, xorForestBuckets, List.length_cons, finMapList_length]
    omega
  let wCin0 : Wire n := rSys (idxAx ⟨0, hL⟩ cfg.qCin0)
  let tWires : List (Wire n) := out.carries
  let rMidPG : QRegister (4 - s) n := rPG.slice s (4 - s) (by omega)
  let uWires : Fin (4 - s) → Wire n := fun j ↦
    optWireOrZero wZero (out.sumWires.get ⟨j.val, by omega⟩)
  have hu_T : ∀ j, uWires j ∉ rMidPG.image := fun j hm_t ↦ by
    have hm_pg : uWires j ∈ rPG.image := QRegister.image_compose_subset rPG _ hm_t
    dsimp only [uWires] at hm_pg
    cases hget : out.sumWires.get ⟨j.val, by omega⟩ with
    | none =>
        rw [hget] at hm_pg
        dsimp only [optWireOrZero, wZero] at hm_pg
        rcases (QRegister.mem_image rPG _).mp hm_pg with ⟨i, hi⟩
        exact hdisj_PW.ne i ⟨st + (4 - s), by omega⟩ hi
    | some w =>
        rw [hget] at hm_pg
        dsimp only [optWireOrZero] at hm_pg
        rcases hspec.2.2.2.2.1 _ (List.get_mem _ _) w hget with ⟨B, hB, hwB⟩ | ⟨k, hk, _, _, rfl⟩
        · exact hB_PG B hB w hwB hm_pg
        · rcases (QRegister.mem_image rPG _).mp hm_pg with ⟨i, hi⟩
          exact hdisj_PW.ne i ⟨k, hk⟩ hi
  have hu_C : ∀ j, uWires j ∉ rGid.image := fun j hm_c ↦ by
    rcases (QRegister.mem_image rGid _).mp hm_c with ⟨i, hi⟩
    have hi' : rGid i = rWork ⟨st + i.val, by omega⟩ := by
      rw [QRegister.slice_apply]
      exact congrArg rWork (Fin.ext (by simp))
    rw [hi'] at hi
    dsimp only [uWires] at hi
    cases hget : out.sumWires.get ⟨j.val, by omega⟩ with
    | none =>
        rw [hget] at hi
        dsimp only [optWireOrZero, wZero] at hi
        have hv := congrArg Fin.val (rWork.wires.injective hi)
        dsimp at hv
        omega
    | some w =>
        rw [hget] at hi
        dsimp only [optWireOrZero] at hi
        rcases hspec.2.2.2.2.1 _ (List.get_mem _ _) w hget with ⟨B, hB, hwB⟩ | ⟨k, hk, _, hk_lt,
            rfl⟩
        · exact hB_anc B hB w hwB ((QRegister.mem_image rWork _).mpr ⟨_, hi⟩)
        · have hv := congrArg Fin.val (rWork.wires.injective hi)
          dsimp at hv
          have := hspec.2.1
          omega
  have hdisj_TC : rMidPG.DisjointWires rGid := (hdisj_PW.compose_left _).compose_right _
  have hwcin_not_B := xorForestBuckets_wcin_not_mem s cfg L hL rSys idxAx hinj_ax
  have hcin_u : ∀ j, wCin0 ≠ uWires j := fun j heq ↦ by
    dsimp only [uWires] at heq
    cases hget : out.sumWires.get ⟨j.val, by omega⟩ with
    | none =>
        rw [hget] at heq; dsimp only [optWireOrZero, wZero, wCin0] at heq
        exact hdisj_SW.ne _ ⟨st + (4 - s), by omega⟩ heq
    | some w =>
        rw [hget] at heq; dsimp only [optWireOrZero] at heq
        rcases hspec.2.2.2.2.1 _ (List.get_mem _ _) w hget with ⟨B, hB, hwB⟩ | ⟨k, hk, _, _, rfl⟩
        · rw [← heq] at hwB
          exact hwcin_not_B B hB hwB
        · exact hdisj_SW.ne _ ⟨k, hk⟩ heq
  have hcin_T : wCin0 ∉ rMidPG.image := fun hm_t ↦ by
    rcases (QRegister.mem_image rPG _).mp (QRegister.image_compose_subset rPG _ hm_t) with ⟨i, hi⟩
    exact hdisj_SP.ne _ i hi.symm
  have hcin_C : wCin0 ∉ rGid.image := fun hm_c ↦ by
    rcases (QRegister.mem_image rWork _).mp (QRegister.image_compose_subset rWork _ hm_c) with ⟨k,
        hk⟩
    exact hdisj_SW.ne _ k hk.symm
  let coreDyn : DynamicCircuit Var n := if inv then
      (DynamicCircuit.circuit (tDagList tWires)).seq ((gidneyApexInvDyn v (4 - s) uWires
      rMidPG rGid wCin0 hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C).seq (DynamicCircuit.circuit
      Circuit.identity)) else (DynamicCircuit.circuit (tList tWires)).seq ((gidneyApexChainDyn
      v false (4 - s) uWires rMidPG rGid wCin0 hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C).seq
      (DynamicCircuit.circuit Circuit.identity))
  (DynamicCircuit.circuit c_xor_fwd).seq
    ((symWrapDynList v out.steps coreDyn).seq
      (DynamicCircuit.circuit c_xor_inv))

def xorForestBatchFwdDyn {kSys mWork : ℕ} (v : Var) (s : ℕ) (cfg : ForestSlotConfig s) (L : ℕ)
    (hs : s ≤ 3) (hL : 1 ≤ L) (hm : xorForestBatchWork s cfg L ≤ mWork)
    (rSys : QRegister kSys n) (rPG : QRegister 7 n) (rWork : QRegister mWork n)
    (hdisj_SP : rSys.DisjointWires rPG) (hdisj_SW : rSys.DisjointWires rWork)
    (hdisj_PW : rPG.DisjointWires rWork) (idxAx : Fin L → Fin 6 → Fin kSys) (hinj_ax :
    Function.Injective (fun p : Fin L × Fin 6 ↦ idxAx p.1 p.2)) : DynamicCircuit Var n :=
    xorForestBatchDyn false v s cfg L hs hL hm rSys rPG rWork hdisj_SP hdisj_SW hdisj_PW idxAx
    hinj_ax

def xorForestBatchInvDyn {kSys mWork : ℕ} (v : Var) (s : ℕ) (cfg : ForestSlotConfig s) (L : ℕ)
    (hs : s ≤ 3) (hL : 1 ≤ L) (hm : xorForestBatchWork s cfg L ≤ mWork)
    (rSys : QRegister kSys n) (rPG : QRegister 7 n) (rWork : QRegister mWork n)
    (hdisj_SP : rSys.DisjointWires rPG) (hdisj_SW : rSys.DisjointWires rWork)
    (hdisj_PW : rPG.DisjointWires rWork) (idxAx : Fin L → Fin 6 → Fin kSys) (hinj_ax :
    Function.Injective (fun p : Fin L × Fin 6 ↦ idxAx p.1 p.2)) : DynamicCircuit Var n :=
    xorForestBatchDyn true v s cfg L hs hL hm rSys rPG rWork hdisj_SP hdisj_SW hdisj_PW idxAx
    hinj_ax

theorem xorForestBatch_spec {kSys mWork : ℕ} (v : Var) (s : ℕ) (cfg : ForestSlotConfig s)
    (L : ℕ) (hs : s ≤ 3) (hL : 1 ≤ L) (hm : xorForestBatchWork s cfg L ≤ mWork)
    (rSys : QRegister kSys n) (rPG : QRegister 7 n) (rWork : QRegister mWork n)
    (hdisj_SP : rSys.DisjointWires rPG) (hdisj_SW : rSys.DisjointWires rWork)
    (hdisj_PW : rPG.DisjointWires rWork) (idxAx : Fin L → Fin 6 → Fin kSys) (hinj_ax :
    Function.Injective (fun p : Fin L × Fin 6 ↦ idxAx p.1 p.2)) : (xorForestBatchFwdDyn v s
    cfg L hs hL hm rSys rPG rWork hdisj_SP hdisj_SW hdisj_PW idxAx hinj_ax).count TOFF = 0 ∧
    (xorForestBatchFwdDyn v s cfg L hs hL hm rSys rPG rWork hdisj_SP hdisj_SW hdisj_PW idxAx
    hinj_ax).count .T = xorForestBatchTCost s cfg L ∧ (xorForestBatchInvDyn v s cfg L hs hL hm
    rSys rPG rWork hdisj_SP hdisj_SW hdisj_PW idxAx hinj_ax).count TOFF = 0 ∧
    (xorForestBatchInvDyn v s cfg L hs hL hm rSys rPG rWork hdisj_SP hdisj_SW hdisj_PW idxAx
    hinj_ax).count .T = xorForestBatchTCost s cfg L ∧ (∀ [Fintype Var] [DecidableEq Var], ∃ (Φ
    : BitAssignment kSys → ℤ) (uLow : BitAssignment kSys → ℕ), (∀ γ : BitAssignment kSys, Φ γ
    + ((2 ^ s * uLow γ : ℕ) : ℤ) = ∑ l : Fin L, (forestAxisNat s cfg (fun i ↦ γ (idxAx l i)) :
    ℤ)) ∧ RealizesEmbeddedUnitaryWithCleanWorkspace (rSys.concat rPG hdisj_SP) rWork
    (apexCatUnitary kSys s hs Φ uLow) (xorForestBatchFwdDyn v s cfg L hs hL hm rSys rPG rWork
    hdisj_SP hdisj_SW hdisj_PW idxAx hinj_ax) ∧ RealizesEmbeddedUnitaryWithCleanWorkspace
    (rSys.concat rPG hdisj_SP) rWork (apexCatUnitary kSys s hs Φ uLow)⁻¹ (xorForestBatchInvDyn
    v s cfg L hs hL hm rSys rPG rWork hdisj_SP hdisj_SW hdisj_PW idxAx hinj_ax)) := by
  let wpairs := batchCnotPairs rSys cfg.pairs idxAx
  have hne_fwd : ∀ wp ∈ wpairs, wp.1 ≠ wp.2 := batchCnotPairs_hne rSys cfg.pairs cfg.hne idxAx
      hinj_ax
  have hne_inv : ∀ wp ∈ wpairs.reverse, wp.1 ≠ wp.2 := fun wp hwp ↦ hne_fwd wp (List.mem_reverse.mp
      hwp)
  have hwp_sys : ∀ wp ∈ wpairs, wp.1 ∈ rSys.image ∧ wp.2 ∈ rSys.image :=
    batchCnotPairs_mem_sys rSys cfg.pairs idxAx
  let c_xor_fwd : Circuit n := cnotPairsCircuit wpairs hne_fwd
  let c_xor_inv : Circuit n := cnotPairsCircuit wpairs.reverse hne_inv
  let buckets := xorForestBuckets s cfg L hL rSys idxAx
  have hmap_len := xorForestBuckets_map_len s cfg L hL rSys idxAx
  have hsteps_eq : compressStepsCount buckets 0 = compressStepsNat (xorForestBucketsLen s cfg L) 0
      := by
    rw [compressStepsCount_eq_nat, hmap_len]
  have hfit_csa : 0 + compressStepsCount buckets 0 ≤ mWork := by
    dsimp only [xorForestBatchWork] at hm
    rw [hsteps_eq]
    omega
  have hB_nodup := xorForestBuckets_nodup s cfg L hL rSys idxAx hinj_ax
  have hB_disj := xorForestBuckets_disj s cfg L hL rSys idxAx hinj_ax
  have hB_sys := xorForestBuckets_sys s cfg L hL rSys idxAx
  have hB_anc : ∀ B ∈ buckets, ∀ x ∈ B, x ∉ rWork.image := fun B hB x hx hm_w ↦ by
    rcases (QRegister.mem_image rSys x).mp (hB_sys B hB x hx) with ⟨i, rfl⟩
    rcases (QRegister.mem_image rWork _).mp hm_w with ⟨k, hk⟩
    exact hdisj_SW.ne i k hk.symm
  have hB_PG : ∀ B ∈ buckets, ∀ x ∈ B, x ∉ rPG.image := fun B hB x hx hm_pg ↦ by
    rcases (QRegister.mem_image rSys x).mp (hB_sys B hB x hx) with ⟨i, rfl⟩
    rcases (QRegister.mem_image rPG _).mp hm_pg with ⟨k, hk⟩
    exact hdisj_SP.ne i k hk.symm
  let out := compressBuckets rWork buckets 0 hfit_csa hB_nodup hB_disj hB_anc
  have hspec := compressBuckets_spec rPG.image rWork
    (disjWires_image (QRegExt.disjointWires_symm hdisj_PW)) buckets 0 hfit_csa hB_nodup hB_disj
      hB_anc hB_PG
  have hst : out.steps.length = compressStepsNat (xorForestBucketsLen s cfg L) 0 :=
    hspec.2.1.trans hsteps_eq
  have hcar_len : out.carries.length = finalCarriesNat (xorForestBucketsLen s cfg L) 0 := by
    rw [compressBuckets_carries_length, hmap_len]
  refine ⟨by
      unfold xorForestBatchFwdDyn xorForestBatchDyn
      simp only [Bool.false_eq_true, ↓reduceIte, count_dyn_seq, count_dyn_circuit,
          count_cnotPairsCircuit_toff,
        count_symWrapDynList_toff, count_tList_toff, count_gidneyApexChainDyn_toff, count_cir_id],
    by
      unfold xorForestBatchFwdDyn xorForestBatchDyn xorForestBatchTCost
      simp only [Bool.false_eq_true, ↓reduceIte, count_dyn_seq, count_dyn_circuit,
          count_cnotPairsCircuit_t,
        count_symWrapDynList_t, count_tList_t, count_gidneyApexChainDyn_t, count_cir_id]
      rw [hst, hcar_len]
      omega,
    by
      unfold xorForestBatchInvDyn xorForestBatchDyn
      simp only [↓reduceIte, count_dyn_seq, count_dyn_circuit, count_cnotPairsCircuit_toff,
        count_symWrapDynList_toff, count_tDagList_toff, count_gidneyApexInvDyn_toff, count_cir_id],
    by
      unfold xorForestBatchInvDyn xorForestBatchDyn xorForestBatchTCost
      simp only [↓reduceIte, count_dyn_seq, count_dyn_circuit, count_cnotPairsCircuit_t,
        count_symWrapDynList_t, count_tDagList_t, count_gidneyApexInvDyn_t, count_cir_id]
      rw [hst, hcar_len]
      omega,
    ?_⟩
  intro _ _
  let st := out.steps.length
  have hm' : 1 + st + (4 - s) ≤ mWork := by
    dsimp only [xorForestBatchWork] at hm
    omega
  let rGid : QRegister (4 - s) n := rWork.slice (0 + st) (4 - s) (by omega)
  let wZero : Wire n := rWork ⟨st + (4 - s), by omega⟩
  have hblen : buckets.length = 4 - s := by
    simp only [buckets, xorForestBuckets, List.length_cons, finMapList_length]
    omega
  have hsw_len : out.sumWires.length = 4 - s := hspec.1.trans hblen
  let wCin0 : Wire n := rSys (idxAx ⟨0, hL⟩ cfg.qCin0)
  let tWires : List (Wire n) := out.carries
  let rMidPG : QRegister (4 - s) n := rPG.slice s (4 - s) (by omega)
  let uWires : Fin (4 - s) → Wire n := fun j ↦
    optWireOrZero wZero (out.sumWires.get ⟨j.val, by omega⟩)
  have hu_T : ∀ j, uWires j ∉ rMidPG.image := fun j hm_t ↦ by
    have hm_pg : uWires j ∈ rPG.image := QRegister.image_compose_subset rPG _ hm_t
    dsimp only [uWires] at hm_pg
    cases hget : out.sumWires.get ⟨j.val, by omega⟩ with
    | none =>
        rw [hget] at hm_pg
        dsimp only [optWireOrZero, wZero] at hm_pg
        rcases (QRegister.mem_image rPG _).mp hm_pg with ⟨i, hi⟩
        exact hdisj_PW.ne i ⟨st + (4 - s), by omega⟩ hi
    | some w =>
        rw [hget] at hm_pg
        dsimp only [optWireOrZero] at hm_pg
        rcases hspec.2.2.2.2.1 _ (List.get_mem _ _) w hget with ⟨B, hB, hwB⟩ | ⟨k, hk, _, _, rfl⟩
        · exact hB_PG B hB w hwB hm_pg
        · rcases (QRegister.mem_image rPG _).mp hm_pg with ⟨i, hi⟩
          exact hdisj_PW.ne i ⟨k, hk⟩ hi
  have hu_C : ∀ j, uWires j ∉ rGid.image := fun j hm_c ↦ by
    rcases (QRegister.mem_image rGid _).mp hm_c with ⟨i, hi⟩
    have hi' : rGid i = rWork ⟨st + i.val, by omega⟩ := by
      rw [QRegister.slice_apply]
      exact congrArg rWork (Fin.ext (by simp))
    rw [hi'] at hi
    dsimp only [uWires] at hi
    cases hget : out.sumWires.get ⟨j.val, by omega⟩ with
    | none =>
        rw [hget] at hi
        dsimp only [optWireOrZero, wZero] at hi
        have hv := congrArg Fin.val (rWork.wires.injective hi)
        dsimp at hv
        omega
    | some w =>
        rw [hget] at hi
        dsimp only [optWireOrZero] at hi
        rcases hspec.2.2.2.2.1 _ (List.get_mem _ _) w hget with ⟨B, hB, hwB⟩ | ⟨k, hk, _, hk_lt,
            rfl⟩
        · exact hB_anc B hB w hwB ((QRegister.mem_image rWork _).mpr ⟨_, hi⟩)
        · have hv := congrArg Fin.val (rWork.wires.injective hi)
          dsimp at hv
          have := hspec.2.1
          omega
  have hdisj_TC : rMidPG.DisjointWires rGid := (hdisj_PW.compose_left _).compose_right _
  have hwcin_not_B := xorForestBuckets_wcin_not_mem s cfg L hL rSys idxAx hinj_ax
  have hcin_u : ∀ j, wCin0 ≠ uWires j := fun j heq ↦ by
    dsimp only [uWires] at heq
    cases hget : out.sumWires.get ⟨j.val, by omega⟩ with
    | none =>
        rw [hget] at heq; dsimp only [optWireOrZero, wZero, wCin0] at heq
        exact hdisj_SW.ne _ ⟨st + (4 - s), by omega⟩ heq
    | some w =>
        rw [hget] at heq; dsimp only [optWireOrZero] at heq
        rcases hspec.2.2.2.2.1 _ (List.get_mem _ _) w hget with ⟨B, hB, hwB⟩ | ⟨k, hk, _, _, rfl⟩
        · rw [← heq] at hwB
          exact hwcin_not_B B hB hwB
        · exact hdisj_SW.ne _ ⟨k, hk⟩ heq
  have hcin_T : wCin0 ∉ rMidPG.image := fun hm_t ↦ by
    rcases (QRegister.mem_image rPG _).mp (QRegister.image_compose_subset rPG _ hm_t) with ⟨i, hi⟩
    exact hdisj_SP.ne _ i hi.symm
  have hcin_C : wCin0 ∉ rGid.image := fun hm_c ↦ by
    rcases (QRegister.mem_image rWork _).mp (QRegister.image_compose_subset rWork _ hm_c) with ⟨k,
        hk⟩
    exact hdisj_SW.ne _ k hk.symm
  let f_xor_fwd : BitAssignment n → BitAssignment n := cnotPairsPerm wpairs
  let f_xor_inv : BitAssignment n → BitAssignment n := cnotPairsPerm wpairs.reverse
  let β₂_of : BitAssignment kSys → BitAssignment n :=
    fun γ ↦ symStepFwdList out.steps (f_xor_fwd (canonAssign rSys γ))
  let Φ : BitAssignment kSys → ℤ := fun γ ↦ 16 * (wireListSum tWires (β₂_of γ) : ℤ)
  let uLow : BitAssignment kSys → ℕ :=
    fun γ ↦ weightedOptWiresVal out.sumWires (β₂_of γ) + (β₂_of γ wCin0).val
  have hU_steps : ∀ s' ∈ out.steps, s'.S ⊆ rSys.image ∪ rWork.image := fun s' hs' w hw ↦ by
    rcases hspec.2.2.2.2.2.2.1 s' hs' w hw with ⟨B, hB, hwB⟩ | ⟨k, hk, _, _, rfl⟩
    · exact Finset.mem_union_left _ (hB_sys B hB w hwB)
    · exact Finset.mem_union_right _ ((QRegister.mem_image rWork _).mpr ⟨⟨k, hk⟩, rfl⟩)
  have hcin0_unchanged : ∀ δ : BitAssignment n, symStepFwdList out.steps δ wCin0 = δ wCin0 :=
    fun δ ↦ symStepFwdList_outside out.steps δ wCin0 fun s' hs' hm_s ↦ by
      rcases hspec.2.2.2.2.2.2.1 s' hs' _ hm_s with ⟨B, hB, hwB⟩ | ⟨k, hk, _, _, heq⟩
      · exact hwcin_not_B B hB hwB
      · exact hdisj_SW.ne _ ⟨k, hk⟩ heq
  have hxor_fwd_outside_sys : ∀ (δ : BitAssignment n) (w : Wire n), w ∉ rSys.image → f_xor_fwd
      δ w = δ w := fun δ w hw ↦ cnotPairsPerm_outside wpairs δ w fun wp hwp heq ↦ hw
      (heq ▸ (hwp_sys wp hwp).2)
  have hxor_inv_outside_sys : ∀ (δ : BitAssignment n) (w : Wire n), w ∉ rSys.image → f_xor_inv
      δ w = δ w := fun δ w hw ↦ cnotPairsPerm_outside wpairs.reverse δ w fun wp hwp heq ↦ hw
      (heq ▸ (hwp_sys wp (List.mem_reverse.mp hwp)).2)
  have hag_U : ∀ (β : BitAssignment n), (∀ j : Fin mWork, β (rWork j) = 0) →
      ∀ w ∈ rSys.image ∪ rWork.image,
        symStepFwdList out.steps (f_xor_fwd β) w = β₂_of (fun i ↦ β (rSys i)) w := by
    intro β hzero
    let γ : BitAssignment kSys := fun i ↦ β (rSys i)
    refine symStepFwdList_eq_on_superset out.steps hU_steps ?_
    refine cnotPairsPerm_eq_on_superset wpairs (fun wp hwp ↦ ⟨Finset.mem_union_left _ (hwp_sys
      wp hwp).1, Finset.mem_union_left _ (hwp_sys wp hwp).2⟩) fun w hw ↦ ?_
    rcases Finset.mem_union.mp hw with hws | hww
    · rcases (QRegister.mem_image rSys w).mp hws with ⟨i, rfl⟩
      exact (canonAssign_apply_sys rSys γ i).symm
    · have hnot_sys : w ∉ rSys.image := fun hm_s ↦ by
        rcases (QRegister.mem_image rSys w).mp hm_s with ⟨i, rfl⟩
        rcases (QRegister.mem_image rWork _).mp hww with ⟨j, hj⟩
        exact hdisj_SW.ne i j hj.symm
      rw [canonAssign_apply_outside rSys γ hnot_sys]
      rcases (QRegister.mem_image rWork w).mp hww with ⟨j, rfl⟩
      exact hzero j
  have hsum_Φ_uLow : ∀ γ : BitAssignment kSys, Φ γ + ((2 ^ s * uLow γ : ℕ) : ℤ) = ∑ l : Fin L,
      (forestAxisNat s cfg (fun i ↦ γ (idxAx l i)) : ℤ) := by
    intro γ
    let β₁ := f_xor_fwd (canonAssign rSys γ)
    have hzero_canon : ∀ k, 0 ≤ k → (hk : k < mWork) → β₁ (rWork ⟨k, hk⟩) = 0 := fun k _ hk ↦ by
      have hnot_sys : rWork ⟨k, hk⟩ ∉ rSys.image := fun hm_s ↦ by
        rcases (QRegister.mem_image rSys _).mp hm_s with ⟨i, hi⟩
        exact hdisj_SW.ne i ⟨k, hk⟩ hi
      dsimp only [β₁]
      rw [hxor_fwd_outside_sys _ _ hnot_sys, canonAssign_apply_outside rSys γ hnot_sys]
    have hcons := hspec.2.2.2.2.2.2.2 β₁ hzero_canon
    rw [hblen] at hcons
    have hscale_csa : 2 ^ s * weightedOptWiresVal out.sumWires (β₂_of γ) +
        16 * wireListSum out.carries (β₂_of γ) = 2 ^ s * weightedBucketsVal buckets β₁ := by
      have hp4 : 2 ^ s * 2 ^ (4 - s) = 16 := two_pow_mul_four_sub s hs
      calc 2 ^ s * weightedOptWiresVal out.sumWires (β₂_of γ) +
            16 * wireListSum out.carries (β₂_of γ)
          = 2 ^ s * (weightedOptWiresVal out.sumWires (β₂_of γ) +
              2 ^ (4 - s) * wireListSum out.carries (β₂_of γ)) := by
              rw [mul_add, ← mul_assoc, hp4]
        _ = 2 ^ s * weightedBucketsVal buckets β₁ := congrArg (2 ^ s * ·) hcons
    have hcin0_eq : (β₂_of γ wCin0).val = (β₁ wCin0).val :=
      congrArg ZMod.val (hcin0_unchanged β₁)
    have hnat_eq : 16 * wireListSum tWires (β₂_of γ) + 2 ^ s * uLow γ =
        ∑ l : Fin L, forestAxisNat s cfg (fun i ↦ γ (idxAx l i)) := by
      dsimp only [tWires, uLow]
      calc 16 * wireListSum out.carries (β₂_of γ) +
            2 ^ s * (weightedOptWiresVal out.sumWires (β₂_of γ) + (β₂_of γ wCin0).val)
          = 2 ^ s * (β₂_of γ wCin0).val +
            (2 ^ s * weightedOptWiresVal out.sumWires (β₂_of γ) +
              16 * wireListSum out.carries (β₂_of γ)) := by ring
        _ = 2 ^ s * ((β₁ wCin0).val + weightedBucketsVal buckets β₁) := by
              rw [hcin0_eq, hscale_csa]; ring
        _ = ∑ l : Fin L, forestAxisNat s cfg (fun i ↦ γ (idxAx l i)) :=
              weightedBuckets_forest_eq s cfg hL rSys idxAx hinj_ax γ
    dsimp only [Φ]
    calc (16 * (wireListSum tWires (β₂_of γ) : ℤ)) + ((2 ^ s * uLow γ : ℕ) : ℤ)
        = ((16 * wireListSum tWires (β₂_of γ) + 2 ^ s * uLow γ : ℕ) : ℤ) := by push_cast; ring
      _ = ∑ l : Fin L, (forestAxisNat s cfg (fun i ↦ γ (idxAx l i)) : ℤ) := by
          rw [hnat_eq]; push_cast; rfl
  have hhc_xor_fwd : PhasePerm rSys.image c_xor_fwd (fun _ ↦ 1) f_xor_fwd :=
    PhasePerm.of_classicalPerm (classicalPerm_cnotPairsCircuit wpairs hne_fwd) hxor_fwd_outside_sys
  have hhc_xor_inv : PhasePerm rSys.image c_xor_inv (fun _ ↦ 1) f_xor_inv :=
    PhasePerm.of_classicalPerm (classicalPerm_cnotPairsCircuit wpairs.reverse hne_inv)
        hxor_inv_outside_sys
  have hcancel_xor : ∀ (f_m : BitAssignment n → BitAssignment n),
      (∀ δ w, w ∉ rPG.image → f_m δ w = δ w) →
      ∀ β w, w ∉ rPG.image → f_xor_inv (f_m (f_xor_fwd β)) w = β w := by
    intro f_m hout_m β w hw
    let S_nonPG : Finset (Wire n) := Finset.univ \ rPG.image
    have hmem_S : ∀ u : Wire n, u ∈ S_nonPG ↔ u ∉ rPG.image := by simp [S_nonPG]
    have hsys_S : ∀ u ∈ rSys.image, u ∈ S_nonPG := fun u hu ↦
      (hmem_S u).mpr fun hpg ↦ by
        rcases (QRegister.mem_image rSys u).mp hu with ⟨i, rfl⟩
        rcases (QRegister.mem_image rPG _).mp hpg with ⟨j, hj⟩
        exact hdisj_SP.ne i j hj.symm
    have heq_inv := cnotPairsPerm_eq_on_superset (S := S_nonPG) wpairs.reverse
      (fun wp hwp ↦ by
        have hs := hwp_sys wp (List.mem_reverse.mp hwp)
        exact ⟨hsys_S _ hs.1, hsys_S _ hs.2⟩)
      (β₁ := f_m (f_xor_fwd β)) (β₂ := f_xor_fwd β)
      (fun u hu ↦ hout_m (f_xor_fwd β) u ((hmem_S u).mp hu))
      w ((hmem_S w).mpr hw)
    dsimp only [f_xor_inv, f_xor_fwd] at heq_inv ⊢
    rw [heq_inv, cnotPairsPerm_reverse_cancel wpairs hne_fwd β]
  have hpg_not_sys : ∀ j : Fin 7, rPG j ∉ rSys.image := fun j hm_s ↦ by
    rcases (QRegister.mem_image rSys _).mp hm_s with ⟨i, hi⟩
    exact hdisj_SP.ne i j hi
  have hpg_xor_eq : ∀ (f_m : BitAssignment n → BitAssignment n) (β : BitAssignment n),
      regVal rPG (f_xor_inv (f_m (f_xor_fwd β))) = regVal rPG (f_m (f_xor_fwd β)) :=
    fun f_m β ↦ regVal_congr rPG fun j ↦ hxor_inv_outside_sys _ (rPG j) (hpg_not_sys j)
  have hpg_in_eq : ∀ (β : BitAssignment n) (j : Fin 7),
      symStepFwdList out.steps (f_xor_fwd β) (rPG j) = β (rPG j) := fun β j ↦ by
    rw [symStepFwdList_outside out.steps (f_xor_fwd β) (rPG j) (fun s' hs' hm_s ↦ by
      rcases hspec.2.2.2.2.2.2.1 s' hs' _ hm_s with ⟨B, hB, hwB⟩ | ⟨k, hk, _, _, heq⟩
      · exact hB_PG B hB _ hwB ((QRegister.mem_image rPG _).mpr ⟨j, rfl⟩)
      · exact hdisj_PW.ne j ⟨k, hk⟩ heq)]
    exact hxor_fwd_outside_sys β (rPG j) (hpg_not_sys j)
  have hpg_reg_in : ∀ β : BitAssignment n, regVal rPG (symStepFwdList out.steps (f_xor_fwd β))
      = regVal rPG β := fun β ↦ regVal_congr rPG (hpg_in_eq β)
  have hmid_reg_in : ∀ β : BitAssignment n,
      regVal rMidPG (symStepFwdList out.steps (f_xor_fwd β)) =
        ((regVal rPG β) / 2 ^ s) % 2 ^ (4 - s) := fun β ↦ by
    rw [regVal_midSlice7_eq s hs rPG _, hpg_reg_in β]
  have hwork_not_sys : ∀ k : Fin mWork, rWork k ∉ rSys.image := fun k hm_s ↦ by
    rcases (QRegister.mem_image rSys _).mp hm_s with ⟨i, hi⟩
    exact hdisj_SW.ne i k hi
  have hgid_zero_β₂ : ∀ β : BitAssignment n, (∀ j : Fin mWork, β (rWork j) = 0) →
      ∀ i : Fin (4 - s), symStepFwdList out.steps (f_xor_fwd β) (rGid i) = 0 := by
    intro β hzero i
    have hi' : rGid i = rWork ⟨st + i.val, by omega⟩ := by
      rw [QRegister.slice_apply]; exact congrArg rWork (Fin.ext (by simp))
    rw [hi', symStepFwdList_outside out.steps (f_xor_fwd β) _ (fun s' hs' hm_s ↦ by
      rcases hspec.2.2.2.2.2.2.1 s' hs' _ hm_s with ⟨B, hB, hwB⟩ | ⟨k, hk, _, hk_lt, heq⟩
      · exact hB_anc B hB _ hwB ((QRegister.mem_image rWork _).mpr ⟨_, rfl⟩)
      · have hv := congrArg Fin.val (rWork.wires.injective heq)
        dsimp at hv; have := hspec.2.1; omega)]
    rw [hxor_fwd_outside_sys β _ (hwork_not_sys ⟨st + i.val, by omega⟩)]
    exact hzero ⟨st + i.val, by omega⟩
  have huLow_on_β : ∀ β : BitAssignment n, (∀ j : Fin mWork, β (rWork j) = 0) → bitsVal
      (fun j ↦ symStepFwdList out.steps (f_xor_fwd β) (uWires j)) +
      (symStepFwdList out.steps (f_xor_fwd β) wCin0).val = uLow (fun i ↦ β (rSys i)) := by
    intro β hzero
    let γ : BitAssignment kSys := fun i ↦ β (rSys i)
    let δ := symStepFwdList out.steps (f_xor_fwd β)
    have hag := hag_U β hzero
    have hz_δ : δ wZero = 0 := by
      dsimp only [δ]
      rw [hag wZero (Finset.mem_union_right _ ((QRegister.mem_image rWork _).mpr ⟨_, rfl⟩))]
      dsimp only [β₂_of]
      rw [symStepFwdList_outside out.steps _ wZero (fun s' hs' hm_s ↦ by
          rcases hspec.2.2.2.2.2.2.1 s' hs' _ hm_s with ⟨B, hB, hwB⟩ | ⟨k, hk, _, hk_lt, heq⟩
          · exact hB_anc B hB _ hwB ((QRegister.mem_image rWork _).mpr ⟨_, rfl⟩)
          · have hv := congrArg Fin.val (rWork.wires.injective heq)
            dsimp [wZero] at hv; have := hspec.2.1; omega),
        hxor_fwd_outside_sys _ _ (hwork_not_sys ⟨st + (4 - s), by omega⟩),
        canonAssign_apply_outside rSys γ (hwork_not_sys ⟨st + (4 - s), by omega⟩)]
    have hbv := weightedOptWiresVal_eq_bitsVal wZero out.sumWires hsw_len δ hz_δ
    dsimp only [uWires]
    rw [hbv]
    have hsw_eq_u : weightedOptWiresVal out.sumWires δ =
        weightedOptWiresVal out.sumWires (β₂_of γ) :=
      weightedOptWiresVal_congr fun ow how w hsome ↦
        hag w (by
          rcases hspec.2.2.2.2.1 ow how w hsome with ⟨B, hB, hwB⟩ | ⟨k, hk, _, _, rfl⟩
          · exact Finset.mem_union_left _ (hB_sys B hB w hwB)
          · exact Finset.mem_union_right _ ((QRegister.mem_image rWork _).mpr ⟨⟨k, hk⟩, rfl⟩))
    have hcin_u_eq : δ wCin0 = β₂_of γ wCin0 :=
      hag wCin0 (Finset.mem_union_left _ ((QRegister.mem_image rSys _).mpr ⟨_, rfl⟩))
    change weightedOptWiresVal out.sumWires δ + (δ wCin0).val = uLow γ
    rw [hsw_eq_u, hcin_u_eq]
  have htWires_on_β : ∀ β : BitAssignment n, (∀ j : Fin mWork, β (rWork j) = 0) →
      wireListSum tWires (symStepFwdList out.steps (f_xor_fwd β)) =
        wireListSum tWires (β₂_of (fun i ↦ β (rSys i))) := by
    intro β hzero
    refine wireListSum_congr fun w hw ↦ hag_U β hzero w ?_
    rcases hspec.2.2.2.1 w hw with ⟨k, hk, _, rfl⟩
    exact Finset.mem_union_right _ ((QRegister.mem_image rWork _).mpr ⟨⟨k, hk⟩, rfl⟩)
  have hMid_sub_PG : rMidPG.image ⊆ rPG.image := QRegister.image_compose_subset rPG _
  refine ⟨Φ, uLow, hsum_Φ_uLow, ?_, ?_⟩
  · obtain ⟨φ_add, f_add, hp_add0, hval_add, hwp_add⟩ := gidneyApexChain_correct v false
      (4 - s) uWires rMidPG rGid wCin0 hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C
    have hp_add : PhasePerm rPG.image _ φ_add f_add := hp_add0.mono hMid_sub_PG
    have hcpp_gid : CleanPhasePerm rGid rPG.image (gidneyApexChainDyn v false (4 - s) uWires
        rMidPG rGid wCin0 hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C) (gidneyApexChainCircuit
        false (4 - s) uWires rMidPG rGid wCin0 hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C) φ_add
        f_add := ⟨hp_add, fun Q ↦ gidneyApexChainDyn_wp_const v false (4 - s) uWires rMidPG
        rGid wCin0 hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C Q, fun Q ↦ hwp_add _ fun _ _ ↦ rfl⟩
    have hcpp_in0 := cleanPhasePerm_sandwich_phase
      (tList tWires) Circuit.identity _ (fun _ ↦ 1) id id
      (phasePerm_tList tWires) (PhasePerm.identity ∅) (Finset.disjoint_empty_left _) hcpp_gid
    have hcpp_in : CleanPhasePerm rGid rPG.image
        ((DynamicCircuit.circuit (tList tWires)).seq
          ((gidneyApexChainDyn v false (4 - s) uWires rMidPG rGid wCin0
              hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C).seq
            (DynamicCircuit.circuit Circuit.identity)))
        (tList tWires ;;ᶜ
          gidneyApexChainCircuit false (4 - s) uWires rMidPG rGid wCin0
            hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C ;;ᶜ
          Circuit.identity)
        _ f_add :=
      CleanPhasePerm.mono_work_and_set hcpp_in0 (Finset.Subset.refl _) (by simp)
    have ⟨f_mid, hp_mid, hM_mid, hwp_mid⟩ := symWrapDynList_phasePerm_correct v rPG.image
        rWork 0 (4 - s) out.steps hspec.2.2.2.2.2.1 (by omega) _ _ _ _ hcpp_in.phasePerm
        (restrictAssertionToZeroAncilla_sandwich_var v rGid ∅ (tList tWires) Circuit.identity
        _ id (phasePerm_tList tWires) (Finset.disjoint_empty_left _) _ _ hwp_add)
    have hcpp_mid : CleanPhasePerm rWork rPG.image (symWrapDynList v out.steps
        ((DynamicCircuit.circuit (tList tWires)).seq ((gidneyApexChainDyn v false (4 - s)
        uWires rMidPG rGid wCin0 hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C).seq
        (DynamicCircuit.circuit Circuit.identity)))) (symWrapCircuitList out.steps _) _ f_mid
        := CleanPhasePerm.mono_work_and_set ⟨hp_mid, fun Q ↦ symWrapDynList_wp_const v
        out.steps _ hcpp_in.wp_const Q, fun Q ↦ hwp_mid _ fun _ _ ↦ rfl⟩
        (QRegister.image_compose_subset rWork _) (Finset.Subset.refl _)
    have hcpp_tot := cleanPhasePerm_sandwich_phase c_xor_fwd c_xor_inv (fun _ ↦ 1) (fun _ ↦ 1)
      f_xor_fwd f_xor_inv hhc_xor_fwd hhc_xor_inv (disjWires_image hdisj_SW) hcpp_mid
    refine cleanPhasePerm_realizes_genCatPhasePerm hdisj_SP hcpp_tot
      (fun γ ↦ midSlicePerm7 s hs (uLow γ)) (fun γ m ↦ Φ γ + 16 * (((((m.val / 2 ^ s) % 2 ^ (4
      - s)) + uLow γ) / 2 ^ (4 - s) : ℕ) : ℤ)) (fun β hzero ↦ ?_)
      (fun β q hq ↦ hcancel_xor f_mid hp_mid.outside β q hq) (fun β hzero ↦ ?_)
    · let δ := symStepFwdList out.steps (f_xor_fwd β)
      obtain ⟨hφ_a, _⟩ := hval_add δ (hgid_zero_β₂ β hzero)
      dsimp only [id, Φ]
      simp only [one_mul, mul_one]
      change dyadicTurn 7 (16 * (wireListSum tWires δ : ℤ)) * φ_add δ = _
      rw [htWires_on_β β hzero, hφ_a, dyadicTurn_add]
      congr 1
      have hS_eq : regVal rMidPG δ + bitsVal (fun j ↦ δ (uWires j)) + (δ wCin0).val =
          ((regVal rPG β) / 2 ^ s) % 2 ^ (4 - s) + uLow (fun i ↦ β (rSys i)) := by
        rw [hmid_reg_in β, add_assoc, huLow_on_β β hzero]
      rw [hS_eq]
      simp
    · let δ := symStepFwdList out.steps (f_xor_fwd β)
      obtain ⟨_, hreg_a⟩ := hval_add δ (hgid_zero_β₂ β hzero)
      dsimp only [Function.comp_apply]
      rw [hpg_xor_eq f_mid β]
      have hreg_m : regVal rPG (f_mid (f_xor_fwd β)) = regVal rPG (f_add δ) :=
        regVal_congr rPG fun j ↦ hM_mid (f_xor_fwd β) (rPG j) ((QRegister.mem_image rPG _).mpr ⟨j,
            rfl⟩)
      rw [hreg_m, regVal_after_midSlice7 s hs rPG f_add δ (hp_add0.outside δ),
        hpg_reg_in β, hreg_a, hmid_reg_in β, add_assoc, huLow_on_β β hzero]
      rfl
  · rw [apexCatUnitary, genCatPhasePermUnitary_inv]
    obtain ⟨φ_sub, f_sub, hcpp_sub0, hval_sub, hwp_sub⟩ := gidneyApexInv_correct v (4 - s)
        uWires rMidPG rGid wCin0 hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C
    have hcpp_gid : CleanPhasePerm rGid rPG.image (gidneyApexInvDyn v (4 - s) uWires rMidPG
        rGid wCin0 hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C) (gidneyApexInvCircuit (4 - s)
        uWires rMidPG rGid wCin0 hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C) φ_sub f_sub :=
        CleanPhasePerm.mono_work_and_set hcpp_sub0 (Finset.Subset.refl _) hMid_sub_PG
    have hcpp_in0 := cleanPhasePerm_sandwich_phase
      (tDagList tWires) Circuit.identity _ (fun _ ↦ 1) id id
      (phasePerm_tDagList tWires) (PhasePerm.identity ∅) (Finset.disjoint_empty_left _) hcpp_gid
    have hcpp_in : CleanPhasePerm rGid rPG.image
        ((DynamicCircuit.circuit (tDagList tWires)).seq
          ((gidneyApexInvDyn v (4 - s) uWires rMidPG rGid wCin0
              hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C).seq
            (DynamicCircuit.circuit Circuit.identity)))
        (tDagList tWires ;;ᶜ
          gidneyApexInvCircuit (4 - s) uWires rMidPG rGid wCin0
            hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C ;;ᶜ
          Circuit.identity)
        _ f_sub :=
      CleanPhasePerm.mono_work_and_set hcpp_in0 (Finset.Subset.refl _) (by simp)
    have ⟨f_mid, hp_mid, hM_mid, hwp_mid⟩ := symWrapDynList_phasePerm_correct
      v rPG.image rWork 0 (4 - s) out.steps hspec.2.2.2.2.2.1 (by omega)
      _ _ _ _ hcpp_in.phasePerm
      (restrictAssertionToZeroAncilla_sandwich_var v rGid ∅ (tDagList tWires) Circuit.identity
        _ id (phasePerm_tDagList tWires) (Finset.disjoint_empty_left _) _ _ hwp_sub)
    have hcpp_mid : CleanPhasePerm rWork rPG.image (symWrapDynList v out.steps
        ((DynamicCircuit.circuit (tDagList tWires)).seq ((gidneyApexInvDyn v (4 - s) uWires
        rMidPG rGid wCin0 hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C).seq (DynamicCircuit.circuit
        Circuit.identity)))) (symWrapCircuitList out.steps _) _ f_mid :=
        CleanPhasePerm.mono_work_and_set ⟨hp_mid, fun Q ↦ symWrapDynList_wp_const v out.steps
        _ hcpp_in.wp_const Q, fun Q ↦ hwp_mid _ fun _ _ ↦ rfl⟩
        (QRegister.image_compose_subset rWork _) (Finset.Subset.refl _)
    have hcpp_tot := cleanPhasePerm_sandwich_phase c_xor_fwd c_xor_inv (fun _ ↦ 1) (fun _ ↦ 1)
      f_xor_fwd f_xor_inv hhc_xor_fwd hhc_xor_inv (disjWires_image hdisj_SW) hcpp_mid
    refine cleanPhasePerm_realizes_genCatPhasePerm hdisj_SP hcpp_tot
      (fun γ ↦ (midSlicePerm7 s hs (uLow γ)).symm) (fun γ k ↦ -(Φ γ + 16 *
      (((((((midSlicePerm7 s hs (uLow γ)).symm k).val / 2 ^ s) % 2 ^ (4 - s)) + uLow γ) / 2 ^
      (4 - s) : ℕ) : ℤ))) (fun β hzero ↦ ?_)
      (fun β q hq ↦ hcancel_xor f_mid hp_mid.outside β q hq) (fun β hzero ↦ ?_)
    · let γ : BitAssignment kSys := fun i ↦ β (rSys i)
      let δ := symStepFwdList out.steps (f_xor_fwd β)
      let k : Fin (2 ^ 7) := ⟨regVal rPG β, regVal_lt_two_pow rPG β⟩
      let W := 2 ^ (4 - s)
      have hW : 0 < W := by positivity
      let m' := (midSlicePerm7 s hs (uLow γ)).symm k
      have hek : midSlicePerm7 s hs (uLow γ) m' = k :=
        (midSlicePerm7 s hs (uLow γ)).apply_symm_apply k
      have hm'_mid_lt : (m'.val / 2 ^ s) % W < W := Nat.mod_lt _ hW
      have hk_mid : ((m'.val / 2 ^ s) % W + uLow γ) % W = (k.val / 2 ^ s) % W := by
        have hlo : m'.val % 2 ^ s < 2 ^ s := Nat.mod_lt _ (by positivity)
        have hmid : ((m'.val / 2 ^ s) % W + uLow γ) % W < W := Nat.mod_lt _ hW
        have hhi : m'.val / 16 < 8 := by have := m'.isLt; omega
        have hp2 := (pack7Slices_parts s hs _ _ _ hlo hmid hhi).2.1
        have hval_eq : pack7Slices s (m'.val % 2 ^ s) (((m'.val / 2 ^ s) % W + uLow γ) % W)
            (m'.val / 16) = k.val := congrArg Fin.val hek
        rw [hval_eq] at hp2
        exact hp2.symm
      have hdiv_eq : ((W - 1 - ((k.val / 2 ^ s) % W)) + uLow γ) / W =
          (((m'.val / 2 ^ s) % W) + uLow γ) / W := by
        rw [← hk_mid]
        exact ones_complement_div_eq W ((m'.val / 2 ^ s) % W) (uLow γ) hW hm'_mid_lt
      obtain ⟨hφ_s, _⟩ := hval_sub δ (hgid_zero_β₂ β hzero)
      dsimp only [id, Φ]
      simp only [one_mul, mul_one]
      change dyadicTurn 7 (-16 * (wireListSum tWires δ : ℤ)) * φ_sub δ = _
      rw [htWires_on_β β hzero, hφ_s, dyadicTurn_add]
      congr 1
      have hS_inv : (W - 1 - regVal rMidPG δ) + bitsVal (fun j ↦ δ (uWires j)) + (δ wCin0).val
          = (W - 1 - ((k.val / 2 ^ s) % W)) + uLow γ := by
        rw [hmid_reg_in β, add_assoc, huLow_on_β β hzero]
      change -16 * (wireListSum tWires (β₂_of γ) : ℤ) + (-16 : ℤ) * (((((W - 1 - regVal rMidPG
        δ) + bitsVal (fun j ↦ δ (uWires j)) + (δ wCin0).val) / W : ℕ) : ℤ)) = -(16 *
        (wireListSum tWires (β₂_of γ) : ℤ) + 16 * (((((m'.val / 2 ^ s) % W + uLow γ) / W : ℕ)
        : ℤ)))
      rw [hS_inv, hdiv_eq]
      ring
    · let δ := symStepFwdList out.steps (f_xor_fwd β)
      obtain ⟨_, hreg_s⟩ := hval_sub δ (hgid_zero_β₂ β hzero)
      dsimp only [Function.comp_apply]
      rw [hpg_xor_eq f_mid β]
      have hreg_m : regVal rPG (f_mid (f_xor_fwd β)) = regVal rPG (f_sub δ) :=
        regVal_congr rPG fun j ↦ hM_mid (f_xor_fwd β) (rPG j) ((QRegister.mem_image rPG _).mpr ⟨j,
            rfl⟩)
      rw [hreg_m, regVal_after_midSlice7 s hs rPG f_sub δ (hcpp_sub0.phasePerm.outside δ),
        hpg_reg_in β, hreg_s, hmid_reg_in β, add_assoc, huLow_on_β β hzero]
      rfl
attribute [irreducible] xorForestBatchDyn xorForestBatchFwdDyn xorForestBatchInvDyn
end ApexButterflyEngine128
def idxForestAx (off L : ℕ) (_hoff : off + L ≤ 654) (l : Fin L) (q : Fin 6) :
    Fin (3924 + 3) :=
  ⟨6 * (off + l.val) + q.val, by omega⟩
theorem idxForestAx_inj (off L : ℕ) (hoff : off + L ≤ 654) :
    Function.Injective (fun p : Fin L × Fin 6 ↦ idxForestAx off L hoff p.1 p.2) := by
  intro ⟨l₁, q₁⟩ ⟨l₂, q₂⟩ h
  have hv := congrArg Fin.val h
  dsimp only [idxForestAx] at hv
  have hl : l₁.val = l₂.val := by have := q₁.isLt; have := q₂.isLt; omega
  have hq : q₁.val = q₂.val := by omega
  exact Prod.ext (Fin.ext hl) (Fin.ext hq)
def forestTermAxis (φ6 : Fin 64 → ℤ) (γ : BitAssignment (3924 + 3)) (a : ℕ) : ℤ :=
  if ha : a < 654 then
    φ6 ((basisBitsEquiv 6).symm fun q : Fin 6 ↦ γ ⟨6 * a + q.val, by omega⟩)
  else 0
def xorForestBatchFwdDyn128 (s off L : ℕ) (cfg : ForestSlotConfig s) (hs : s ≤ 3) (hL : 1 ≤ L)
    (hoff : off + L ≤ 654) (hwMax : xorForestBatchWork s cfg L ≤ 128) : DynamicCircuit Unit
    nCanon4062 := xorForestBatchFwdDyn () s cfg L hs hL (le_refl (xorForestBatchWork s cfg L))
    rSysCanon128 rPGCanon128 (rWorkCanon128.slice 0 (xorForestBatchWork s cfg L) (Nat.zero_add
    _ ▸ hwMax)) rSysCanon128_disjoint_rPGCanon128
    (rSysCanon128_disjoint_rWorkCanon128.compose_right _)
    (rPGCanon128_disjoint_rWorkCanon128.compose_right _) (idxForestAx off L hoff)
    (idxForestAx_inj off L hoff)
def xorForestBatchInvDyn128 (s off L : ℕ) (cfg : ForestSlotConfig s) (hs : s ≤ 3) (hL : 1 ≤ L)
    (hoff : off + L ≤ 654) (hwMax : xorForestBatchWork s cfg L ≤ 128) : DynamicCircuit Unit
    nCanon4062 := xorForestBatchInvDyn () s cfg L hs hL (le_refl (xorForestBatchWork s cfg L))
    rSysCanon128 rPGCanon128 (rWorkCanon128.slice 0 (xorForestBatchWork s cfg L) (Nat.zero_add
    _ ▸ hwMax)) rSysCanon128_disjoint_rPGCanon128
    (rSysCanon128_disjoint_rWorkCanon128.compose_right _)
    (rPGCanon128_disjoint_rWorkCanon128.compose_right _) (idxForestAx off L hoff)
    (idxForestAx_inj off L hoff)
theorem xorForestBatch128_exists (s off L : ℕ) (cfg : ForestSlotConfig s) (φ6 : Fin 64 → ℤ)
    (hφ6 : ∀ u : Fin 64, (forestAxisNat s cfg (basisBits 6 u) : ℤ) = φ6 u) (hs : s ≤ 3)
    (hL : 1 ≤ L) (hoff : off + L ≤ 654) (hwMax : xorForestBatchWork s cfg L ≤ 128) : ∃ uCat :
    Unitary (2 ^ (3924 + 3 + 7)), (xorForestBatchFwdDyn128 s off L cfg hs hL hoff hwMax).count
    TOFF = 0 ∧ (xorForestBatchInvDyn128 s off L cfg hs hL hoff hwMax).count TOFF = 0 ∧
    (xorForestBatchFwdDyn128 s off L cfg hs hL hoff hwMax).count .T = xorForestBatchTCost s
    cfg L ∧ (xorForestBatchInvDyn128 s off L cfg hs hL hoff hwMax).count .T =
    xorForestBatchTCost s cfg L ∧ RealizesEmbeddedUnitaryWithCleanWorkspace rQftCanon128
    rWorkCanon128 uCat (xorForestBatchFwdDyn128 s off L cfg hs hL hoff hwMax) ∧
    RealizesEmbeddedUnitaryWithCleanWorkspace rQftCanon128 rWorkCanon128 uCat⁻¹
    (xorForestBatchInvDyn128 s off L cfg hs hL hoff hwMax) ∧ (∀ {N : ℕ} [NeZero (2 ^ N)] (rId
    : QRegister (3924 + 3) N) (rPG : QRegister 7 N) (hdisj : rId.DisjointWires rPG) (U_cat7 :
    Unitary (2 ^ 7)), U_cat7.1.mulVec (Pi.single 0 1) = DyadicQft64.phaseGradKet 7 →
    DyadicQft64.IntertwinesCatOp (rPG.embedUnitary U_cat7).1 (rPG.basisOutcomeProjector 0)
    ((rId.concat rPG hdisj).embedUnitary uCat).1 (rId.embedUnitary
    (DyadicQft64.dyadicDiagUnitary (3924 + 3) 7 (fun γ ↦ ∑ r : Fin L, forestTermAxis φ6 γ (off
    + r.val)))).1) := by
  obtain ⟨hToffF, hTF, hToffI, hTI, hRest⟩ := xorForestBatch_spec () s cfg L hs hL
      (le_refl (xorForestBatchWork s cfg L)) rSysCanon128 rPGCanon128 (rWorkCanon128.slice 0
      (xorForestBatchWork s cfg L) (Nat.zero_add _ ▸ hwMax)) rSysCanon128_disjoint_rPGCanon128
      (rSysCanon128_disjoint_rWorkCanon128.compose_right _)
      (rPGCanon128_disjoint_rWorkCanon128.compose_right _) (idxForestAx off L hoff)
      (idxForestAx_inj off L hoff)
  obtain ⟨Φ, uLow, hEqExp, hRF, hRI⟩ := hRest
  refine ⟨apexCatUnitary (3924 + 3) s hs Φ uLow, hToffF, hToffI, hTF, hTI,
    realizes_congr_slice (Nat.zero_add _ ▸ hwMax) (rIdOfCat_concat_rPGOfCat rQftCanon128) hRF,
    realizes_congr_slice (Nat.zero_add _ ▸ hwMax) (rIdOfCat_concat_rPGOfCat rQftCanon128) hRI, ?_⟩
  intro N _ rId rPG hdisj U_cat7 hcol0
  have heff : DyadicQft64.dyadicDiagUnitary (3924 + 3) 7
      (fun γ ↦ Φ γ + ((2 ^ s * uLow γ : ℕ) : ℤ)) = DyadicQft64.dyadicDiagUnitary (3924 + 3) 7
      (fun γ ↦ ∑ r : Fin L, forestTermAxis φ6 γ (off + r.val)) := by
    congr 1; funext γ
    rw [hEqExp γ]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    have ha : off + r.val < 654 := by have := r.isLt; omega
    let b6 : Fin 6 → ZMod 2 := fun q ↦ γ ⟨6 * (off + r.val) + q.val, by omega⟩
    let u6 : Fin 64 := (basisBitsEquiv 6).symm b6
    have hb_eq : b6 = basisBits 6 u6 := ((basisBitsEquiv 6).apply_symm_apply b6).symm
    simp only [forestTermAxis, ha, ↓reduceDIte, idxForestAx]
    change (forestAxisNat s cfg b6 : ℤ) = φ6 u6
    rw [hb_eq]
    exact hφ6 u6
  rw [← heff]
  exact apexCatUnitary_intertwinesCat s hs rId rPG hdisj U_cat7 hcol0 Φ uLow
/-- `CanonStageSpec128` constructor for an `L`-axis Hadamard-Forest CSA+Gidney batch. -/
noncomputable def xorForestBatchCanonStage128 (s off L tB : ℕ) (cfg : ForestSlotConfig s)
    (φ6 : Fin 64 → ℤ) (hφ6 : ∀ u : Fin 64, (forestAxisNat s cfg (basisBits 6 u) : ℤ) = φ6 u)
    (hs : s ≤ 3) (hL : 1 ≤ L) (hoff : off + L ≤ 654)
    (hwMax : xorForestBatchWork s cfg L ≤ 128)
    (htB : xorForestBatchTCost s cfg L = tB) : CanonStageSpec128 where
  uCat := Classical.choose (xorForestBatch128_exists s off L cfg φ6 hφ6 hs hL hoff hwMax)
  uEff := DyadicQft64.dyadicDiagUnitary (3924 + 3) 7
    (fun γ ↦ ∑ r : Fin L, forestTermAxis φ6 γ (off + r.val))
  tCost := tB
  dFwd := xorForestBatchFwdDyn128 s off L cfg hs hL hoff hwMax
  dInv := xorForestBatchInvDyn128 s off L cfg hs hL hoff hwMax
  hToffFwd := (Classical.choose_spec (xorForestBatch128_exists s off L cfg φ6 hφ6 hs hL hoff
      hwMax)).1
  hToffInv := (Classical.choose_spec (xorForestBatch128_exists s off L cfg φ6 hφ6 hs hL hoff
      hwMax)).2.1
  hTFwd := (Classical.choose_spec (xorForestBatch128_exists s off L cfg φ6 hφ6 hs hL hoff
      hwMax)).2.2.1.trans htB
  hTInv := (Classical.choose_spec (xorForestBatch128_exists s off L cfg φ6 hφ6 hs hL hoff
      hwMax)).2.2.2.1.trans htB
  hRealFwd := (Classical.choose_spec (xorForestBatch128_exists s off L cfg φ6 hφ6 hs hL hoff
      hwMax)).2.2.2.2.1
  hRealInv := (Classical.choose_spec (xorForestBatch128_exists s off L cfg φ6 hφ6 hs hL hoff
      hwMax)).2.2.2.2.2.1
  hIntertwines := (Classical.choose_spec (xorForestBatch128_exists s off L cfg φ6 hφ6 hs hL hoff
      hwMax)).2.2.2.2.2.2
noncomputable def diag6Unitary (φ : Fin 64 → ℤ) : Unitary 64 :=
  ⟨Matrix.diagonal fun u : Fin 64 ↦ omega128 (φ u), by
    rw [Matrix.mem_unitaryGroup_iff']
    change (Matrix.diagonal _)ᴴ * Matrix.diagonal _ = 1
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext u
    exact star_mul_omega128_self _⟩
def w16Ctrl (k : Fin 5) : Fin 6 := ⟨k.val + 1, by omega⟩
def w16Tgt (k : Fin 5) : Fin 6 := ⟨k.val, by omega⟩
theorem w16Ctrl_ne_tgt (k : Fin 5) : w16Ctrl k ≠ w16Tgt k := by
  fin_cases k <;> decide
def w16AxisCircuit (k : Fin 5) : Circuit 6 :=
    (Circuit.CNOT (w16Ctrl k) (w16Tgt k) (w16Ctrl_ne_tgt k)).seq ((Circuit.T (w16Tgt k)).seq
    (Circuit.CNOT (w16Ctrl k) (w16Tgt k) (w16Ctrl_ne_tgt k)))
def w16Exp6 (k : Fin 5) (u : Fin 64) : ℤ :=
  16 * (bitXor (bit6 u (w16Ctrl k)) (bit6 u (w16Tgt k)) : ℤ)
theorem w16AxisCircuit_eval (k : Fin 5) :
    (w16AxisCircuit k).eval = diag6Unitary (w16Exp6 k) := by
  apply Subtype.ext
  apply phasePerm_to_diagonal6 (w16AxisCircuit k)
  let m : Fin 6 := w16Ctrl k
  let t : Fin 6 := w16Tgt k
  have hne : m ≠ t := w16Ctrl_ne_tgt k
  let fc : BitAssignment 6 → BitAssignment 6 := fun γ ↦ Function.update γ t (γ t + γ m)
  have hcnot : PhasePerm ({t} : Finset (Wire 6)) (Circuit.CNOT m t hne) (fun _ ↦ 1) fc :=
    PhasePerm.of_classicalPerm (ClassicalPerm.CNOT m t hne) (fun γ w hw ↦ by
      have hwt : w ≠ t := by simpa using hw
      exact Function.update_of_ne hwt _ _)
  have htail := ((PhasePerm.gateT t).mono (Finset.empty_subset _)).seq hcnot
  have hfull := hcnot.seq htail
  have hperm_id : ((fc ∘ id) ∘ fc) = (id : BitAssignment 6 → BitAssignment 6) := by
    funext β w
    dsimp only [Function.comp_apply, id_eq, fc]
    by_cases hwt : w = t
    · subst hwt
      rw [Function.update_self, Function.update_of_ne hne, Function.update_self,
        zmod2_add_cancel_right]
    · rw [Function.update_of_ne hwt, Function.update_of_ne hwt]
  have hp0 : PhasePerm (∅ : Finset (Wire 6)) (w16AxisCircuit k)
      (fun β ↦ 1 * (dyadicTurn 7 (16 * (fc β t).val) * 1)) id := by
    refine { evolve := fun β ↦ ?_, outside := fun _ _ _ ↦ rfl }
    have hev := hfull.evolve β
    rw [hperm_id] at hev
    exact hev
  refine PhasePerm.congr_phase hp0 fun β ↦ ?_
  simp only [one_mul, mul_one]
  congr 1
  have hxor : ∀ a b : ZMod 2, ((b + a).val : ℤ) = (bitXor a.val b.val : ℤ) := by decide
  dsimp only [fc, w16Exp6, m, t]
  rw [Function.update_self, hxor (β (w16Ctrl k)) (β (w16Tgt k)),
    bit6_basisBitsEquiv_symm, bit6_basisBitsEquiv_symm]
/-- `L`-axis weight-16 stage on `CanonStageSpec128` (`L` `T` gates, `TOFF = 0`). -/
noncomputable def stageW16PrefixCanonStage128 (L : ℕ) (hL : L ≤ 654) (k : Fin 5) :
    CanonStageSpec128 :=
  (CanonStageSpec128.ofAxisPrefixCircuit L hL (w16AxisCircuit k) (diag6Unitary (w16Exp6 k)) 1
    (by fin_cases k <;> decide)
    (by fin_cases k <;> decide)
    (by fin_cases k <;> decide)
    (by fin_cases k <;> decide)
    (w16AxisCircuit_eval k)).congr
    (uEff' := axisProdPrefix L hL (fun _ ↦ diag6Unitary (w16Exp6 k)))
    (tCost' := L) rfl (Nat.mul_one L)
def forestCfg3 : ForestSlotConfig 3 where
  pairs := [(5, 3)]
  hne := by decide
  qCin0 := 3
  col0Tail6 := []
  colRest6 := Fin.elim0
  hCinNotTail := by decide
  hTailNodup := by decide
  hRestNodup := fun r ↦ Fin.elim0 r
  hCinDisjRest := fun r ↦ Fin.elim0 r
  hTailDisjRest := fun r ↦ Fin.elim0 r
  hRestDisj := fun r ↦ Fin.elim0 r
def forestExp3 (u : Fin 64) : ℤ := 8 * (bitXor (bit6 u 5) (bit6 u 3) : ℤ)
theorem forestCfg3_exp_eq : ∀ u : Fin 64, (forestAxisNat 3 forestCfg3 (basisBits 6 u) : ℤ) =
    forestExp3 u := by
  decide
def forestCfg2 : ForestSlotConfig 2 where
  pairs := [(4, 1), (2, 4), (5, 2)]
  hne := by decide
  qCin0 := 1
  col0Tail6 := [2]
  colRest6 := fun _ ↦ [4]
  hCinNotTail := by decide
  hTailNodup := by decide
  hRestNodup := by decide
  hCinDisjRest := by decide
  hTailDisjRest := by decide
  hRestDisj := by decide
def forestExp2 (u : Fin 64) : ℤ := 4 * (bitXor (bit6 u 4) (bit6 u 1) : ℤ) + 4 *
    (bitXor (bit6 u 5) (bit6 u 2) : ℤ) + 8 * (bitXor (bit6 u 4) (bit6 u 2) : ℤ)
theorem forestCfg2_exp_eq : ∀ u : Fin 64, (forestAxisNat 2 forestCfg2 (basisBits 6 u) : ℤ) =
    forestExp2 u := by
  decide
def forestCfg1 : ForestSlotConfig 1 where
  pairs := [(0, 4), (3, 0), (1, 3), (5, 1)]
  hne := by decide
  qCin0 := 4
  col0Tail6 := [1]
  colRest6 := ![([0] : List (Fin 6)), [3]]
  hCinNotTail := by decide
  hTailNodup := by decide
  hRestNodup := by decide
  hCinDisjRest := by decide
  hTailDisjRest := by decide
  hRestDisj := by decide
def forestExp1 (u : Fin 64) : ℤ := 2 * (bitXor (bit6 u 4) (bit6 u 0) : ℤ) + 2 *
    (bitXor (bit6 u 5) (bit6 u 1) : ℤ) + 4 * (bitXor (bit6 u 3) (bit6 u 0) : ℤ) + 8 *
    (bitXor (bit6 u 3) (bit6 u 1) : ℤ)
theorem forestCfg1_exp_eq : ∀ u : Fin 64, (forestAxisNat 1 forestCfg1 (basisBits 6 u) : ℤ) =
    forestExp1 u := by
  decide
def forestCfg0 : ForestSlotConfig 0 where
  pairs := [(0, 5), (0, 2)]
  hne := by decide
  qCin0 := 5
  col0Tail6 := []
  colRest6 := fun r ↦ if r.val = 2 then [2] else []
  hCinNotTail := by decide
  hTailNodup := by decide
  hRestNodup := by decide
  hCinDisjRest := by decide
  hTailDisjRest := by decide
  hRestDisj := by decide
def forestExp0 (u : Fin 64) : ℤ := 1 * (bitXor (bit6 u 5) (bit6 u 0) : ℤ) + 8 *
    (bitXor (bit6 u 2) (bit6 u 0) : ℤ)
theorem forestCfg0_exp_eq : ∀ u : Fin 64, (forestAxisNat 0 forestCfg0 (basisBits 6 u) : ℤ) =
    forestExp0 u := by
  decide
/-- 1-electron (`L = 3` axes) Slot-3 Hadamard-Forest stage on `CanonStageSpec128` (`10 T`, `TOFF =
  0`). -/
noncomputable def activeOneElecSlot3Stage128 : CanonStageSpec128 :=
  xorForestBatchCanonStage128 3 0 3 10 forestCfg3 forestExp3 forestCfg3_exp_eq
    (by decide) (by decide) (by decide) (by decide) (by decide)
/-- 1-electron (`L = 3` axes) Slot-2 Hadamard-Forest stage on `CanonStageSpec128` (`27 T`, `TOFF =
  0`). -/
noncomputable def activeOneElecSlot2Stage128 : CanonStageSpec128 :=
  xorForestBatchCanonStage128 2 0 3 27 forestCfg2 forestExp2 forestCfg2_exp_eq
    (by decide) (by decide) (by decide) (by decide) (by decide)
/-- 1-electron (`L = 3` axes) Slot-1 Hadamard-Forest stage on `CanonStageSpec128` (`39 T`, `TOFF =
  0`). -/
noncomputable def activeOneElecSlot1Stage128 : CanonStageSpec128 :=
  xorForestBatchCanonStage128 1 0 3 39 forestCfg1 forestExp1 forestCfg1_exp_eq
    (by decide) (by decide) (by decide) (by decide) (by decide)
/-- 1-electron (`L = 3` axes) Slot-0 Hadamard-Forest stage on `CanonStageSpec128` (`26 T`, `TOFF =
  0`). -/
noncomputable def activeOneElecSlot0Stage128 : CanonStageSpec128 :=
  xorForestBatchCanonStage128 0 0 3 26 forestCfg0 forestExp0 forestCfg0_exp_eq
    (by decide) (by decide) (by decide) (by decide) (by decide)
theorem hL3_le_654 : 3 ≤ 654 := by decide
theorem axisProdPrefix_mul (L : ℕ) (hL : L ≤ 654) (f g : Fin L → Unitary 64) :
    axisProdPrefix L hL f * axisProdPrefix L hL g = axisProdPrefix L hL (fun a ↦ f a * g a) := by
  dsimp only [axisProdPrefix]
  exact prod_ofFn_embedUnitary_mul (rAxisPrefix L hL) (fun _ _ h ↦ rAxisPrefix_disjoint hL h) f g
theorem axisProdPrefix_diag6Unitary_eq_dyadicDiagUnitary (L : ℕ) (hL : L ≤ 654) (φ6 : Fin 64 → ℤ) :
    axisProdPrefix L hL (fun _ ↦ diag6Unitary φ6) =
      DyadicQft64.dyadicDiagUnitary (3924 + 3) 7
        (fun γ ↦ ∑ a : Fin L, forestTermAxis φ6 γ (0 + a.val)) := by
  apply Subtype.ext
  dsimp only [axisProdPrefix]
  have hmap_eq : ((List.ofFn fun a : Fin L ↦ (rAxisPrefix L hL a).embedUnitary (diag6Unitary
      φ6)).map Subtype.val) = (List.ofFn fun a : Fin L ↦ Matrix.diagonal fun x : Fin (2 ^
      (3924 + 3)) ↦ omega128 (φ6 ((rAxisPrefix L hL a).extractIndex x))) := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn; funext a
    rw [Function.comp_apply, QRegister.embedUnitary_val]
    exact PosMomSelectDynamic.embedMatrix_diagonal (rAxisPrefix L hL a) _
  rw [submonoid_coe_list_prod, hmap_eq, prod_ofFn_diagonal, DyadicQft64.dyadicDiagUnitary]
  apply congrArg Matrix.diagonal; funext x
  rw [prod_ofFn_omega128, ← DyadicQft64.dyadicTurn_eq_omega128]
  apply congrArg (DyadicQft64.dyadicTurn 7)
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  have ha : a.val < 654 := Nat.lt_of_lt_of_le a.isLt hL
  simp only [Nat.zero_add, forestTermAxis, ha, ↓reduceDIte]
  apply congrArg φ6
  apply (basisBitsEquiv 6).injective
  rw [(basisBitsEquiv 6).apply_symm_apply]
  funext q
  change basisBits 6 ((rAxisPrefix L hL a).extractIndex x) q = _
  rw [QRegister.basisBits_extractIndex]
  rfl
theorem diag6Unitary_mul_add (φ₁ φ₂ : Fin 64 → ℤ) :
    diag6Unitary φ₁ * diag6Unitary φ₂ = diag6Unitary (fun u ↦ φ₁ u + φ₂ u) := by
  apply Subtype.ext
  change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1; funext u
  exact (omega128_add (φ₁ u) (φ₂ u)).symm
theorem stageDiag6_eq_diag6Unitary (m : Fin 6) :
    stageDiag6 m = diag6Unitary (stageRowExp128 m) := rfl
theorem wireHadamard6_comm_diag6 (m : Fin 6) (φ : Fin 64 → ℤ)
    (hindep : ∀ z w : Fin 64, (∀ r : Fin 6, r ≠ m → bit6 z r = bit6 w r) → φ z = φ w) :
    wireHadamard6 m * diag6Unitary φ = diag6Unitary φ * wireHadamard6 m := by
  apply Subtype.ext
  ext z w
  change ((wireHadamard6 m).1 * Matrix.diagonal (fun u ↦ omega128 (φ u))) z w =
    (Matrix.diagonal (fun u ↦ omega128 (φ u)) * (wireHadamard6 m).1) z w
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  let reg : QRegister 1 6 := QRegister.singleton m
  rw [wireHadamard6, QRegister.embedUnitary_val, reg.embedMatrix_apply]
  by_cases h : (reg.basisSplitEquiv z).2 = (reg.basisSplitEquiv w).2
  · have hOut := (reg.basisSplit_environment_eq_iff z w).mp h
    have hall : ∀ r : Fin 6, r ≠ m → bit6 z r = bit6 w r := fun r hr ↦ by
      have hnot : r ∉ Set.range reg.wires := by
        rintro ⟨idx, hidx⟩
        exact hr hidx.symm
      rw [bit6_eq_basisBits_val, bit6_eq_basisBits_val, hOut r hnot]
    rw [hindep z w hall, mul_comm]
  · simp [h]
def remExp4 (u : Fin 64) : ℤ := 8 * (bitXor (bit6 u 5) (bit6 u 3) : ℤ) + 4 *
    (bitXor (bit6 u 5) (bit6 u 2) : ℤ) + 2 * (bitXor (bit6 u 5) (bit6 u 1) : ℤ) + 1 *
    (bitXor (bit6 u 5) (bit6 u 0) : ℤ)
def remExp3 (u : Fin 64) : ℤ := 8 * (bitXor (bit6 u 4) (bit6 u 2) : ℤ) + 4 *
    (bitXor (bit6 u 4) (bit6 u 1) : ℤ) + 2 * (bitXor (bit6 u 4) (bit6 u 0) : ℤ) + 4 *
    (bitXor (bit6 u 5) (bit6 u 2) : ℤ) + 2 * (bitXor (bit6 u 5) (bit6 u 1) : ℤ) + 1 *
    (bitXor (bit6 u 5) (bit6 u 0) : ℤ)
def remExp2 (u : Fin 64) : ℤ := 8 * (bitXor (bit6 u 3) (bit6 u 1) : ℤ) + 4 *
    (bitXor (bit6 u 3) (bit6 u 0) : ℤ) + 2 * (bitXor (bit6 u 4) (bit6 u 0) : ℤ) + 2 *
    (bitXor (bit6 u 5) (bit6 u 1) : ℤ) + 1 * (bitXor (bit6 u 5) (bit6 u 0) : ℤ)
def remExp1 (u : Fin 64) : ℤ := 8 * (bitXor (bit6 u 2) (bit6 u 0) : ℤ) + 1 *
    (bitXor (bit6 u 5) (bit6 u 0) : ℤ)
theorem forest6_eq_orig6 :
    let h5 := wireHadamard6 5
    let h4 := wireHadamard6 4
    let h3 := wireHadamard6 3
    let h2 := wireHadamard6 2
    let h1 := wireHadamard6 1
    let h0 := wireHadamard6 0
    let s4 := diag6Unitary (w16Exp6 4)
    let s3 := diag6Unitary forestExp3 * diag6Unitary (w16Exp6 3)
    let s2 := diag6Unitary forestExp2 * diag6Unitary (w16Exp6 2)
    let s1 := diag6Unitary forestExp1 * diag6Unitary (w16Exp6 1)
    let s0 := diag6Unitary forestExp0 * diag6Unitary (w16Exp6 0)
    ((((h0 * (s0 * h1)) * (s1 * h2)) * (s2 * h3)) * (s3 * h4)) * (s4 * h5) =
      uCoreHadamard6 := by
  intro h5 h4 h3 h2 h1 h0 s4 s3 s2 s1 s0
  let r4 := diag6Unitary remExp4
  let r3 := diag6Unitary remExp3
  let r2 := diag6Unitary remExp2
  let r1 := diag6Unitary remExp1
  have hd5 : stageDiag6 5 = r4 * s4 := by
    dsimp only [r4, s4]; rw [stageDiag6_eq_diag6Unitary, diag6Unitary_mul_add]
    congr 1; funext u; revert u; decide
  have hc4 : h4 * r4 = r4 * h4 :=
    wireHadamard6_comm_diag6 4 remExp4 fun z w h ↦ by
      dsimp only [remExp4]
      rw [h 5 (by decide), h 3 (by decide), h 2 (by decide), h 1 (by decide), h 0 (by decide)]
  have hd4 : stageDiag6 4 * r4 = r3 * s3 := by
    dsimp only [r4, r3, s3]
    rw [stageDiag6_eq_diag6Unitary, diag6Unitary_mul_add, diag6Unitary_mul_add,
        diag6Unitary_mul_add]
    congr 1; funext u; revert u; decide
  have hc3 : h3 * r3 = r3 * h3 :=
    wireHadamard6_comm_diag6 3 remExp3 fun z w h ↦ by
      dsimp only [remExp3]
      rw [h 5 (by decide), h 4 (by decide), h 2 (by decide), h 1 (by decide), h 0 (by decide)]
  have hd3 : stageDiag6 3 * r3 = r2 * s2 := by
    dsimp only [r3, r2, s2]
    rw [stageDiag6_eq_diag6Unitary, diag6Unitary_mul_add, diag6Unitary_mul_add,
        diag6Unitary_mul_add]
    congr 1; funext u; revert u; decide
  have hc2 : h2 * r2 = r2 * h2 :=
    wireHadamard6_comm_diag6 2 remExp2 fun z w h ↦ by
      dsimp only [remExp2]
      rw [h 5 (by decide), h 4 (by decide), h 3 (by decide), h 1 (by decide), h 0 (by decide)]
  have hd2 : stageDiag6 2 * r2 = r1 * s1 := by
    dsimp only [r2, r1, s1]
    rw [stageDiag6_eq_diag6Unitary, diag6Unitary_mul_add, diag6Unitary_mul_add,
        diag6Unitary_mul_add]
    congr 1; funext u; revert u; decide
  have hc1 : h1 * r1 = r1 * h1 :=
    wireHadamard6_comm_diag6 1 remExp1 fun z w h ↦ by
      dsimp only [remExp1]
      rw [h 5 (by decide), h 2 (by decide), h 0 (by decide)]
  have hd1 : stageDiag6 1 * r1 = s0 := by
    dsimp only [r1, s0]
    rw [stageDiag6_eq_diag6Unitary, diag6Unitary_mul_add, diag6Unitary_mul_add]
    congr 1; funext u; revert u; decide
  unfold uCoreHadamard6
  symm
  calc ((((h0 * (stageDiag6 1 * h1)) * (stageDiag6 2 * h2)) *
          (stageDiag6 3 * h3)) * (stageDiag6 4 * h4)) * (stageDiag6 5 * h5)
      = h0 * stageDiag6 1 * h1 * stageDiag6 2 * h2 * stageDiag6 3 * h3 *
          stageDiag6 4 * (h4 * r4) * s4 * h5 := by
          rw [hd5]; simp only [_root_.mul_assoc]
    _ = h0 * stageDiag6 1 * h1 * stageDiag6 2 * h2 * stageDiag6 3 * h3 *
          (stageDiag6 4 * r4) * h4 * s4 * h5 := by
          rw [hc4]; simp only [_root_.mul_assoc]
    _ = h0 * stageDiag6 1 * h1 * stageDiag6 2 * h2 * stageDiag6 3 *
          (h3 * r3) * s3 * h4 * s4 * h5 := by
          rw [hd4]; simp only [_root_.mul_assoc]
    _ = h0 * stageDiag6 1 * h1 * stageDiag6 2 * h2 * (stageDiag6 3 * r3) *
          h3 * s3 * h4 * s4 * h5 := by
          rw [hc3]; simp only [_root_.mul_assoc]
    _ = h0 * stageDiag6 1 * h1 * stageDiag6 2 * (h2 * r2) * s2 *
          h3 * s3 * h4 * s4 * h5 := by
          rw [hd3]; simp only [_root_.mul_assoc]
    _ = h0 * stageDiag6 1 * h1 * (stageDiag6 2 * r2) * h2 * s2 *
          h3 * s3 * h4 * s4 * h5 := by
          rw [hc2]; simp only [_root_.mul_assoc]
    _ = h0 * stageDiag6 1 * (h1 * r1) * s1 * h2 * s2 *
          h3 * s3 * h4 * s4 * h5 := by
          rw [hd2]; simp only [_root_.mul_assoc]
    _ = h0 * (stageDiag6 1 * r1) * h1 * s1 * h2 * s2 *
          h3 * s3 * h4 * s4 * h5 := by
          rw [hc1]; simp only [_root_.mul_assoc]
    _ = ((((h0 * (s0 * h1)) * (s1 * h2)) * (s2 * h3)) * (s3 * h4)) * (s4 * h5) := by
          rw [hd1]; simp only [_root_.mul_assoc]
/-- Complete 6-stage Hadamard-Forest `QFT_64` `CanonStageSpec128` on the 1 active anchor electron
  (`L = 3` axes,
**`117 T` one-way = `234 T/step`**, `TOFF = 0`, saving **`-26 T/step`** below
`activeOneElecFullQftStage128`'s `130 T`). -/
noncomputable def rawActiveOneElecForestQftStage128 : CanonStageSpec128 :=
    (((stageHPrefixCanonStage128 3 hL3_le_654 5).seq (stageW16PrefixCanonStage128 3 hL3_le_654
    4)).seq (((stageHPrefixCanonStage128 3 hL3_le_654 4).seq ((stageW16PrefixCanonStage128 3
    hL3_le_654 3).seq activeOneElecSlot3Stage128)).seq (((stageHPrefixCanonStage128 3
    hL3_le_654 3).seq ((stageW16PrefixCanonStage128 3 hL3_le_654 2).seq
    activeOneElecSlot2Stage128)).seq (((stageHPrefixCanonStage128 3 hL3_le_654 2).seq
    ((stageW16PrefixCanonStage128 3 hL3_le_654 1).seq activeOneElecSlot1Stage128)).seq
    (((stageHPrefixCanonStage128 3 hL3_le_654 1).seq ((stageW16PrefixCanonStage128 3
    hL3_le_654 0).seq activeOneElecSlot0Stage128)).seq (stageHPrefixCanonStage128 3 hL3_le_654
    0))))))
theorem stage128_seq_uEff (A B : CanonStageSpec128) : (A.seq B).uEff = B.uEff * A.uEff := rfl
theorem stageHPrefix128_uEff (L : ℕ) (hL : L ≤ 654) (kf : Fin 6) :
    (stageHPrefixCanonStage128 L hL kf).uEff = axisProdPrefix L hL (fun _ ↦ wireHadamard6 kf) := rfl
theorem stageW16Prefix128_uEff (L : ℕ) (hL : L ≤ 654) (k : Fin 5) :
    (stageW16PrefixCanonStage128 L hL k).uEff = axisProdPrefix L hL (fun _ ↦ diag6Unitary (w16Exp6
        k)) := rfl
theorem activeOneElecSlot3_128_uEff :
    activeOneElecSlot3Stage128.uEff = axisProdPrefix 3 hL3_le_654 (fun _ ↦ diag6Unitary forestExp3)
        :=
  (axisProdPrefix_diag6Unitary_eq_dyadicDiagUnitary 3 hL3_le_654 forestExp3).symm
theorem activeOneElecSlot2_128_uEff :
    activeOneElecSlot2Stage128.uEff = axisProdPrefix 3 hL3_le_654 (fun _ ↦ diag6Unitary forestExp2)
        :=
  (axisProdPrefix_diag6Unitary_eq_dyadicDiagUnitary 3 hL3_le_654 forestExp2).symm
theorem activeOneElecSlot1_128_uEff :
    activeOneElecSlot1Stage128.uEff = axisProdPrefix 3 hL3_le_654 (fun _ ↦ diag6Unitary forestExp1)
        :=
  (axisProdPrefix_diag6Unitary_eq_dyadicDiagUnitary 3 hL3_le_654 forestExp1).symm
theorem activeOneElecSlot0_128_uEff :
    activeOneElecSlot0Stage128.uEff = axisProdPrefix 3 hL3_le_654 (fun _ ↦ diag6Unitary forestExp0)
        :=
  (axisProdPrefix_diag6Unitary_eq_dyadicDiagUnitary 3 hL3_le_654 forestExp0).symm
theorem rawActiveOneElecForestQftStage128_uEff_eq :
    rawActiveOneElecForestQftStage128.uEff = axisProdPrefix 3 hL3_le_654 (fun _ ↦ uCoreHadamard6)
        := by
  unfold rawActiveOneElecForestQftStage128
  simp only [stage128_seq_uEff, stageHPrefix128_uEff, stageW16Prefix128_uEff,
    activeOneElecSlot3_128_uEff, activeOneElecSlot2_128_uEff,
    activeOneElecSlot1_128_uEff, activeOneElecSlot0_128_uEff, axisProdPrefix_mul]
  exact congrArg (fun u6 ↦ axisProdPrefix 3 hL3_le_654 (fun _ ↦ u6)) forest6_eq_orig6
/-- Complete 6-stage `117-T` 1-electron Hadamard-Forest `QFT_64` `CanonStageSpec128` (`117 T`
  one-way = `234 T/step`, `TOFF = 0`). -/
noncomputable def activeOneElecForestFullQftStage128 : CanonStageSpec128 :=
  rawActiveOneElecForestQftStage128.congr
    (uEff' := axisProdPrefix 3 hL3_le_654 (fun _ ↦ uCoreHadamard6))
    (tCost' := 117)
    rawActiveOneElecForestQftStage128_uEff_eq
    rfl
@[simp] theorem activeOneElecForestFullQftStage128_tCost :
    activeOneElecForestFullQftStage128.tCost = 117 := rfl
/-- `k`-th binary bit (`k : Fin 7`) of a 7-bit momentum sum `s : Fin 128`. -/
def bit7 (s : Fin 128) (k : Fin 7) : ℕ := (s.val / 2 ^ k.val) % 2
/-- The 15 sub-32 Karatsuba XOR terms `∑_{1 ≤ m ≤ 5} ∑_{0 ≤ r < m} 2^{5 - m + r} * (bit6 z m ⊕ bit7
  s r)`
between the upper 5 bits `z_1..z_5` of `z : Fin 64` and the lower 5 bits `s_0..s_4` of `s : Fin
128`. -/
def pointCrossXorExp128 (z : Fin 64) (s : Fin 128) : ℤ := 1 *
    (bitXor (bit6 z 5) (bit7 s 0) : ℤ) + 2 * (bitXor (bit6 z 5) (bit7 s 1) : ℤ) + 2 *
    (bitXor (bit6 z 4) (bit7 s 0) : ℤ) + 4 * (bitXor (bit6 z 5) (bit7 s 2) : ℤ) + 4 *
    (bitXor (bit6 z 4) (bit7 s 1) : ℤ) + 4 * (bitXor (bit6 z 3) (bit7 s 0) : ℤ) + 8 *
    (bitXor (bit6 z 5) (bit7 s 3) : ℤ) + 8 * (bitXor (bit6 z 4) (bit7 s 2) : ℤ) + 8 *
    (bitXor (bit6 z 3) (bit7 s 1) : ℤ) + 8 * (bitXor (bit6 z 2) (bit7 s 0) : ℤ) + 16 *
    (bitXor (bit6 z 5) (bit7 s 4) : ℤ) + 16 * (bitXor (bit6 z 4) (bit7 s 3) : ℤ) + 16 *
    (bitXor (bit6 z 3) (bit7 s 2) : ℤ) + 16 * (bitXor (bit6 z 2) (bit7 s 1) : ℤ) + 16 *
    (bitXor (bit6 z 1) (bit7 s 0) : ℤ)
/-- `0-T` Clifford phase (`S` on `s_1`, `S†` on `s_2..s_5`, `Z` on `s_6`, and 6 parallel `CZ` gates
  on `(z_r, s_r)`). -/
def pointSumCliffordExp128 (z : Fin 64) (s : Fin 128) : ℤ := 32 * (bit7 s 1 : ℤ) + 96 *
    ((bit7 s 2 : ℤ) + (bit7 s 3 : ℤ) + (bit7 s 4 : ℤ) + (bit7 s 5 : ℤ)) + 64 * (bit7 s 6 : ℤ)
    + 64 * ((bit6 z 5 : ℤ) * (bit7 s 5 : ℤ) + (bit6 z 4 : ℤ) * (bit7 s 4 : ℤ) + (bit6 z 3 : ℤ)
    * (bit7 s 3 : ℤ) + (bit6 z 2 : ℤ) * (bit7 s 2 : ℤ) + (bit6 z 1 : ℤ) * (bit7 s 1 : ℤ) +
    (bit6 z 0 : ℤ) * (bit7 s 0 : ℤ))
/-- `z`-independent `0-T` single-electron Clifford phase (`S†` on bit `1` and `S` on bits
  `2..5`). -/
def pointElecCliffordExp128 (u : Fin 64) : ℤ := 96 * (bit6 u 1 : ℤ) + 32 *
    ((bit6 u 2 : ℤ) + (bit6 u 3 : ℤ) + (bit6 u 4 : ℤ) + (bit6 u 5 : ℤ))
/-- `ℕ`-level hybrid 6-bit word packing the lower `c` bits (`q < c`) of `s : Fin 128`
and the upper `6 - c` bits (`c ≤ q < 6`) of `z : Fin 64`. -/
def packHybrid6Nat (z : Fin 64) (s : Fin 128) (c : ℕ) : ℕ :=
    (if 0 < c then bit7 s 0 else bit6 z 0) + 2 * (if 1 < c then bit7 s 1 else bit6 z 1) + 4 *
    (if 2 < c then bit7 s 2 else bit6 z 2) + 8 * (if 3 < c then bit7 s 3 else bit6 z 3) + 16 *
    (if 4 < c then bit7 s 4 else bit6 z 4) + 32 * (if 5 < c then bit7 s 5 else bit6 z 5)
theorem packHybrid6Nat_lt (z : Fin 64) (s : Fin 128) (c : ℕ) : packHybrid6Nat z s c < 64 := by
  have hb7 (k : Fin 7) : bit7 s k < 2 := Nat.mod_lt _ (by decide)
  have hb6 (q : Fin 6) : bit6 z q < 2 := Nat.mod_lt _ (by decide)
  have h0 := hb7 0; have h1 := hb7 1; have h2 := hb7 2
  have h3 := hb7 3; have h4 := hb7 4; have h5 := hb7 5
  have g0 := hb6 0; have g1 := hb6 1; have g2 := hb6 2
  have g3 := hb6 3; have g4 := hb6 4; have g5 := hb6 5
  unfold packHybrid6Nat
  split_ifs <;> omega
def packHybrid6 (z : Fin 64) (s : Fin 128) (c : ℕ) : Fin 64 :=
  ⟨packHybrid6Nat z s c, packHybrid6Nat_lt z s c⟩
def hybridStageExp5 (u : Fin 64) : ℤ := w16Exp6 4 u
def hybridStageExp4 (u : Fin 64) : ℤ := w16Exp6 3 u + forestExp3 u
def hybridStageExp3 (u : Fin 64) : ℤ := w16Exp6 2 u + forestExp2 u
def hybridStageExp2 (u : Fin 64) : ℤ := w16Exp6 1 u + forestExp1 u
def hybridStageExp1 (u : Fin 64) : ℤ := w16Exp6 0 u + forestExp0 u
/-- **Exact 5-Cutoff Hybrid Stage Decomposition of `pointCrossXorExp128 z s`**. -/
theorem pointCrossXorExp128_eq_sum_hybrid_stages : ∀ (z : Fin 64) (s : Fin 128),
    pointCrossXorExp128 z s = hybridStageExp5 (packHybrid6 z s 5) + hybridStageExp4
    (packHybrid6 z s 4) + hybridStageExp3 (packHybrid6 z s 3) + hybridStageExp2
    (packHybrid6 z s 2) + hybridStageExp1 (packHybrid6 z s 1) := by
  decide +kernel
/-- Core register slice `[0 .. fullSysCoreWires mPayload)` inside `fullSysCoreWires mPayload +
  42`. -/
def rCoreInCoreSum42 (mPayload : ℕ) :
    QRegister (fullSysCoreWires mPayload) (fullSysCoreWires mPayload + 42) :=
  QRegister.block 0 (fullSysCoreWires mPayload) (by omega)
/-- Per-axis 14-bit sum register slice `[fullSysCoreWires mPayload + 14 * w .. + 14)` inside
`fullSysCoreWires mPayload + 42`. -/
def rSum14InCoreSum42 (mPayload : ℕ) (w : Fin 3) :
    QRegister 14 (fullSysCoreWires mPayload + 42) :=
  QRegister.block (fullSysCoreWires mPayload + 14 * w.val) 14 (by have := w.isLt; omega)
/-- Generic 3-axis 42-wire sum subspace projector on `fullSysCoreWires mPayload + 42`. -/
noncomputable def pStream42Of {mPayload : ℕ}
    (sumFn : Fin 3 → BitAssignment (fullSysCoreWires mPayload) → ℕ) :
    Operator (2 ^ (fullSysCoreWires mPayload + 42)) :=
  Matrix.diagonal fun x ↦
    let ξ := basisBits (fullSysCoreWires mPayload + 42) x
    let γ : BitAssignment (fullSysCoreWires mPayload) := fun q ↦ ξ (rCoreInCoreSum42 mPayload q)
    if ∀ w : Fin 3, regVal (rSum14InCoreSum42 mPayload w) ξ = sumFn w γ then (1 : ℂ) else 0
end StageAPointPhase128OnStep
namespace HeldStreamEStream42Interface
open MeasureBranchHadamardSem (matrix_ext_ket)
open FullSysCatSegmentBridge (fullSysCoreWires)
open NuclearTwistRealizes (slot2AxisSum)
open InterWalkRSum42Hoist (qreg_block_apply kActOrig kFull80 rAct0 rCoreFull rSum0 rSum14In42
  rSum14Full hAct0_disj_Sum14 hCoreFull_disj_Sum14 hSum14In42_disj E_rawStream42 pSum42Zero
  E_rawStream42_eq_streamProjOp pSum42Zero_mulVec_basisKet streamProjOp_mulVec_basisKet
  rSum0_extractIndex_eq_zero_iff joinActSum streamTarget42 basisBits_streamTarget42 rawStreamVec
  rawStreamOfLow rawStreamOfLow_eq_slot2AxisSum low3924Bits h3924_actOrig
  isLow3924Prefix_rCoreOrig)
open HoistInitStream1300And164 (IsSlot2StreamUnitary uStreamFullOf)
open SpecsAux SpecsAux.SpecMirror
theorem basisBits_symm_apply {k : ℕ} (β : BitAssignment k) : basisBits k
    ((basisBitsEquiv k).symm β) = β := (basisBitsEquiv k).apply_symm_apply β
/-- **3-Axis Stream Computation Identity (`uStreamFullOf 0 * uStreamFullOf 1 * uStreamFullOf 2`)**:
Applying the 3-axis stream unitaries `uStreamFullOf uStream 0 * (uStreamFullOf uStream 1 *
uStreamFullOf uStream 2)`
to `pSum42Zero` produces `E_rawStream42`. -/
theorem uStreamFullOf_012_mul_pSum42Zero_eq_E_rawStream42
    {uStream : Fin 3 → Unitary (2 ^ (fullSysCoreWires 80 + 14))}
    (hStr : IsSlot2StreamUnitary uStream) : (uStreamFullOf uStream 0 * (uStreamFullOf uStream
    1 * uStreamFullOf uStream 2)).1 * pSum42Zero = E_rawStream42 := by
  apply matrix_ext_ket; intro β
  change ((uStreamFullOf uStream 0 * (uStreamFullOf uStream 1 * uStreamFullOf uStream 2)).1 *
    pSum42Zero).mulVec (basisKet β) = E_rawStream42.mulVec (basisKet β)
  rw [E_rawStream42_eq_streamProjOp, ← Matrix.mulVec_mulVec, pSum42Zero_mulVec_basisKet,
    streamProjOp_mulVec_basisKet]
  by_cases h0 : rSum0.extractIndex ((basisBitsEquiv kFull80).symm β) = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
    have hzAll : ∀ j : Fin 42, β (rSum0 j) = 0 := (rSum0_extractIndex_eq_zero_iff β).mp h0
    have hz2 : ∀ i : Fin 14, β (rSum14Full 2 i) = 0 := fun i ↦ hzAll (rSum14In42 2 i)
    obtain ⟨β₂, hk₂, hout₂, hsum₂⟩ := hStr 2 β hz2
    have hCore₂ : (fun q ↦ β₂ (rCoreFull q)) = (fun q ↦ β (rCoreFull q)) :=
      funext fun q ↦ hout₂ _ (fun hm ↦ by
        rcases (QRegister.mem_image _ _).mp hm with ⟨k, hk⟩
        exact (hCoreFull_disj_Sum14 2).ne q k hk.symm)
    have hz1 : ∀ i : Fin 14, β₂ (rSum14Full 1 i) = 0 := fun i ↦ by
      rw [hout₂ _ (fun hm ↦ ?_)]
      · exact hzAll (rSum14In42 1 i)
      · rcases (QRegister.mem_image _ _).mp hm with ⟨k, hk⟩
        exact (hSum14In42_disj (by decide : (2 : Fin 3) ≠ 1)).ne k i (rSum0.wires.injective hk)
    obtain ⟨β₁, hk₁, hout₁, hsum₁⟩ := hStr 1 β₂ hz1
    have hCore₁ : (fun q ↦ β₁ (rCoreFull q)) = (fun q ↦ β (rCoreFull q)) :=
      funext fun q ↦ (hout₁ _ (fun hm ↦ by
        rcases (QRegister.mem_image _ _).mp hm with ⟨k, hk⟩
        exact (hCoreFull_disj_Sum14 1).ne q k hk.symm)).trans (congrFun hCore₂ q)
    have hz0 : ∀ i : Fin 14, β₁ (rSum14Full 0 i) = 0 := fun i ↦ by
      rw [hout₁ _ (fun hm ↦ ?_), hout₂ _ (fun hm ↦ ?_)]
      · exact hzAll (rSum14In42 0 i)
      · rcases (QRegister.mem_image _ _).mp hm with ⟨k, hk⟩
        exact (hSum14In42_disj (by decide : (2 : Fin 3) ≠ 0)).ne k i (rSum0.wires.injective hk)
      · rcases (QRegister.mem_image _ _).mp hm with ⟨k, hk⟩
        exact (hSum14In42_disj (by decide : (1 : Fin 3) ≠ 0)).ne k i (rSum0.wires.injective hk)
    obtain ⟨β₀, hk₀, hout₀, hsum₀⟩ := hStr 0 β₁ hz0
    change (uStreamFullOf uStream 2).1.mulVec (basisKet β) = basisKet β₂ at hk₂
    change (uStreamFullOf uStream 1).1.mulVec (basisKet β₂) = basisKet β₁ at hk₁
    change (uStreamFullOf uStream 0).1.mulVec (basisKet β₁) = basisKet β₀ at hk₀
    simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
    change (uStreamFullOf uStream 0).1.mulVec
      ((uStreamFullOf uStream 1).1.mulVec ((uStreamFullOf uStream 2).1.mulVec (basisKet β))) = _
    rw [hk₂, hk₁, hk₀]
    refine congrArg basisKet ?_
    let y := (basisBitsEquiv kFull80).symm β
    have hRawEq : ∀ w : Fin 3,
        slot2AxisSum w (fun q ↦ β (rCoreFull q)) = rawStreamVec h3924_actOrig (rAct0.extractIndex
            y) w := by
      intro w
      rw [← rawStreamOfLow_eq_slot2AxisSum (fun q ↦ β (rCoreFull q)) w]
      dsimp only [rawStreamVec]
      refine congrFun (congrArg rawStreamOfLow (funext fun q ↦ ?_)) w
      dsimp only [low3924Bits]
      rw [rAct0.basisBits_extractIndex y ⟨q.val, lt_of_lt_of_le q.isLt h3924_actOrig⟩]
      dsimp only [y]
      rw [basisBits_symm_apply]
      have hpre := isLow3924Prefix_rCoreOrig q
      change β (rCoreFull ⟨q.val, _⟩) = β (rAct0 ⟨q.val, _⟩)
      exact congrArg β (congrArg rAct0 hpre)
    funext g
    by_cases hg : g.val < kActOrig
    · have hgAct : g = rAct0 ⟨g.val, hg⟩ := by ext; simp [rAct0]
      have hnot : ∀ w : Fin 3, g ∉ (rSum14Full w).image := fun w hm ↦ by
        rcases (QRegister.mem_image _ _).mp hm with ⟨k, hk⟩
        exact (hAct0_disj_Sum14 w).ne ⟨g.val, hg⟩ k (hgAct.symm.trans hk.symm)
      rw [hout₀ g (hnot 0), hout₁ g (hnot 1), hout₂ g (hnot 2)]
      dsimp only [joinActSum]
      rw [basisBits_symm_apply, dite_eq_left hg, rAct0.basisBits_extractIndex,
        basisBits_symm_apply, ← hgAct]
    · have hlt42 : g.val - kActOrig < 42 := by
        have hk : kFull80 = kActOrig + 42 := rfl
        have := g.isLt
        omega
      let j42 : Fin 42 := ⟨g.val - kActOrig, hlt42⟩
      let w : Fin 3 := ⟨j42.val / 14, by omega⟩
      let i14 : Fin 14 := ⟨j42.val % 14, by omega⟩
      have hjEq : rSum14In42 w i14 = j42 := by
        ext; simp [rSum14In42, w, i14]; omega
      have hgSum : rSum14Full w i14 = g := by
        change rSum0 (rSum14In42 w i14) = g
        rw [hjEq]; ext; simp [rSum0, j42]; omega
      dsimp only [joinActSum]
      rw [basisBits_symm_apply, dite_eq_right hg]
      change β₀ g = basisBits 42 (streamTarget42 (rawStreamVec h3924_actOrig (rAct0.extractIndex
          y))) j42
      rw [← hjEq, basisBits_streamTarget42, ← hgSum, ← hRawEq w]
      have hw3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
      rcases hw3 w with hw | hw | hw <;> rw [hw]
      · rw [hsum₀ i14, hCore₁]
      · have hn0 : rSum14Full 1 i14 ∉ (rSum14Full 0).image := fun hm ↦ by
          rcases (QRegister.mem_image _ _).mp hm with ⟨k, hk⟩
          exact (hSum14In42_disj (by decide : (1 : Fin 3) ≠ 0)).ne i14 k (rSum0.wires.injective
              hk.symm)
        rw [hout₀ _ hn0, hsum₁ i14, hCore₂]
      · have hn0 : rSum14Full 2 i14 ∉ (rSum14Full 0).image := fun hm ↦ by
          rcases (QRegister.mem_image _ _).mp hm with ⟨k, hk⟩
          exact (hSum14In42_disj (by decide : (2 : Fin 3) ≠ 0)).ne i14 k (rSum0.wires.injective
              hk.symm)
        have hn1 : rSum14Full 2 i14 ∉ (rSum14Full 1).image := fun hm ↦ by
          rcases (QRegister.mem_image _ _).mp hm with ⟨k, hk⟩
          exact (hSum14In42_disj (by decide : (2 : Fin 3) ≠ 1)).ne i14 k (rSum0.wires.injective
              hk.symm)
        rw [hout₀ _ hn0, hout₁ _ hn1, hsum₂ i14]
  · rw [ite_eq_right h0, ite_eq_right h0, Matrix.mulVec_zero]
end HeldStreamEStream42Interface
/-!
# Stage-A Origin-`0` Mod-4 Head Phase Reduction
Proves the Origin-`0` reduction of the Stage-A momentum-space Mod-4 Head Phase Oracle (`TOFF = 0`):
1. **Section 1 — 18-Qubit Point-Phase Diagonal Decomposition & Origin-`0` Conjugation Identity
(`uCoreHadamard18_conj_pointPhaseUnitary18Z8_eq_origin0`)**:
   - Decomposes the 18-qubit point-phase diagonal matrix `pointPhaseDiag18 α z := Matrix.diagonal
   (fun x ↦ if x = z then α else 1)`
     as `1 + (α - 1) • Matrix.single z z 1` (`pointPhaseDiag18_eq_one_add_smul_single`).
   - Combines linearity of unitary conjugation with
   `uCoreHadamard18_conj_single_eq_pointDiag18_conj_uHadamard18_zero`
     to prove **`uCoreHadamard18_conj_pointPhaseDiag18_eq_origin0`** and
     **`uCoreHadamard18_conj_pointPhaseUnitary18Z8_eq_origin0`**:
     for any `k : ZMod 8` and any 18-bit target coordinate `z : Fin (2 ^ 18)`,
     $$(uCoreHadamard18)^{-1} \cdot \text{pointPhaseUnitary18Z8 } k\, z \cdot uCoreHadamard18
       = (pointDiagUnitary18\, z)^{-1} \cdot \bigl((uHadamard18)^{-1} \cdot
       \text{pointPhaseUnitary18Z8 } k\, 0 \cdot uHadamard18\bigr) \cdot pointDiagUnitary18\, z.$$
     Every spectator electron `e ∈ 1..217` inside the middle step is tested against the **fixed
     origin `0 : Fin (2 ^ 18)`**
     (`|0^{18}⟩⟨0^{18}|_e`) instead of `z = rElec[0]`!
2. **Section 2 — `uHeadPhaseMod4Origin0` & Exact Commutation with `rElec[0]`
(`uHeadPhaseMod4Origin0_comm_rElec0`)**:
   - Defines `rElec0InCore : QRegister 18 posCoreWires` (`[0 .. 18)`) and `rRest4016InCore :
   QRegister 4016 posCoreWires`
     (`[18 .. 4034)`), with `rElec0InCore_disjoint_rRest4016InCore : rElec0InCore.DisjointWires
     rRest4016InCore`.
   - Defines `uHeadPhaseMod4Origin0 : Unitary (2 ^ posCoreWires)` testing spectator electrons
   `1..217` against
     the origin `0` (independent of `rElec[0]`), proves `uHeadPhaseMod4Origin0_eq_monomialZ8`, and
     proves:
     * **`uHeadPhaseMod4Origin0_comm_rElec0`**: `uHeadPhaseMod4Origin0` commutes with
     `rElec0InCore.embedUnitary U`
       for every 18-qubit unitary `U : Unitary (2 ^ 18)` on Electron `0`, and
     * **`uHeadPhaseMod4Origin0ConjH_comm_rElec0`**: `(uSpectatorHadamard3906)⁻¹ *
     uHeadPhaseMod4Origin0 * uSpectatorHadamard3906`
       also commutes with `rElec0InCore.embedUnitary U`!
3. **Section 3 — 217-Electron Spectator Product Algebra (`elecProd217_mul`, `elecProd217_inv`),
`0-T` Circuit `cHad217`, and `uQft217_conj_uHeadPhaseMod4_eq_pointDiag217_conj_origin0`**:
   - Proves `rSpectatorSlot_disjoint`, `elecProd217_mul`, `elecProd217_one`, and `elecProd217_inv`.
   - Constructs the concrete `0-T`, `0-TOFF` circuit `cHad217 rCore : Circuit n` realizing
   `uHad217` (`dHad217_realizes_core`).
   - Proves **`uQft217_conj_uSpectatorPhase217_eq_pointDiag217_conj_origin0`** and
     **`uQft217_conj_uHeadPhaseMod4_eq_pointDiag217_conj_origin0`**:
     conjugating the 217-electron Mod-4 head operator by `uQft217` (`∏ e ∈ 1..217,
     uCoreHadamard18_e`)
     equals conjugating the origin-`0` Hadamard-sandwiched operator by `pointDiag217 z`!
-/
namespace OriginZeroHeadMod4Reduction
open ZeroAncillaUSP (omega8)
open PosSlots24BranchConcrete (posCoreWires wSlot0Core wHeadThresh rElecSlot slotSubGridCoord64)
open PosHeadMod4_15476 (star_mul_omega8_pow monomialZ8UnitaryN embedUnitary_monomialZ8UnitaryN
  headEnBoolSpec)
open DyadicQft64Engine (wireHadamard6)
open DyadicQft64WalkCircuit (disjoint_block_sep prod_ofFn_embedUnitary_mul)
open StageAPosHeadConjugatedCircuit (rSpectatorElec3906InCore
  uSpectatorHadamard3906 uCoreHadamard18 uHadamard6 uHadamard18 pointDiagUnitary18
  uCoreHadamard18_conj_single_eq_pointDiag18_conj_uHadamard18_zero rSpectatorSlot elecProd217
  uQft217 uHad217 pointDiag217)
/-  18-qubit diagonal matrix applying scalar `α : ℂ` at target basis state `z : Fin (2 ^ 18)`
and `1` on all other basis states `x ≠ z`. -/
open HermitianMat SpecsAux SpecsAux.SpecMirror
open scoped ComplexOrder MatrixOrder Circuit.Notation
def pointPhaseDiag18 (α : ℂ) (z : Fin (2 ^ 18)) : Matrix (Fin (2 ^ 18)) (Fin (2 ^ 18)) ℂ :=
  Matrix.diagonal fun x : Fin (2 ^ 18) ↦ if x = z then α else 1
/-- Exact rank-1 decomposition `pointPhaseDiag18 α z = 1 + (α - 1) • Matrix.single z z 1`. -/
theorem pointPhaseDiag18_eq_one_add_smul_single (α : ℂ) (z : Fin (2 ^ 18)) :
    pointPhaseDiag18 α z = 1 + (α - 1) • Matrix.single z z (1 : ℂ) := by
  ext x y
  by_cases hxy : x = y
  · subst hxy
    by_cases hxz : x = z
    · subst hxz
      simp [pointPhaseDiag18, Matrix.single]
    · simp [pointPhaseDiag18, Matrix.single, hxz, Ne.symm hxz]
  · have hne : ¬ (z = x ∧ z = y) := fun ⟨hzx, hzy⟩ ↦ hxy (hzx.symm.trans hzy)
    simp [pointPhaseDiag18, Matrix.single, hxy, hne]
/-- Linearity of unitary conjugation on `1 + c • M`. -/
theorem unitary_conj_one_add_smul {D : ℕ} (U : Unitary D) (c : ℂ)
    (M : Matrix (Fin D) (Fin D) ℂ) :
    (U⁻¹).1 * (1 + c • M) * U.1 = 1 + c • ((U⁻¹).1 * M * U.1) := by
  have hU : (U⁻¹).1 * U.1 = 1 := U.2.1
  rw[Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hU, Matrix.mul_smul, Matrix.smul_mul]
/-- **18-Qubit Point-Phase Diagonal Origin-`0` Conjugation Identity**:
For any scalar `α : ℂ` and any 18-bit target coordinate `z : Fin (2 ^ 18)`, conjugating
`pointPhaseDiag18 α z` by `uCoreHadamard18` equals conjugating the **origin-`0`** matrix
`pointPhaseDiag18 α 0` by `uHadamard18` followed by `pointDiagUnitary18 z`. -/
theorem uCoreHadamard18_conj_pointPhaseDiag18_eq_origin0 (α : ℂ) (z : Fin (2 ^ 18)) :
    (uCoreHadamard18⁻¹).1 * pointPhaseDiag18 α z * uCoreHadamard18.1 =
    ((pointDiagUnitary18 z)⁻¹).1 * ((uHadamard18⁻¹).1 * pointPhaseDiag18 α 0 * uHadamard18.1)
    * (pointDiagUnitary18 z).1 := by
  rw [pointPhaseDiag18_eq_one_add_smul_single α z,
      pointPhaseDiag18_eq_one_add_smul_single α 0,
      unitary_conj_one_add_smul uCoreHadamard18 (α - 1) (Matrix.single z z (1 : ℂ)),
      unitary_conj_one_add_smul uHadamard18 (α - 1) (Matrix.single 0 0 (1 : ℂ)),
      unitary_conj_one_add_smul (pointDiagUnitary18 z) (α - 1)
        ((uHadamard18⁻¹).1 * Matrix.single 0 0 (1 : ℂ) * uHadamard18.1),
      uCoreHadamard18_conj_single_eq_pointDiag18_conj_uHadamard18_zero z]
/-- 18-qubit `ZMod 8` point-phase unitary applying `omega8 ^ k.val` at `x = z` and `1` at `x ≠
  z`. -/
noncomputable def pointPhaseUnitary18Z8 (k : ZMod 8) (z : Fin (2 ^ 18)) : Unitary (2 ^ 18) :=
  ⟨pointPhaseDiag18 (omega8 ^ k.val) z, by
    rw [Matrix.mem_unitaryGroup_iff']
    change (Matrix.diagonal _)ᴴ * Matrix.diagonal _ = 1
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext x
    dsimp only [Pi.star_apply]
    by_cases hxz : x = z
    · rw [ite_eq_left hxz, star_mul_omega8_pow]
    · rw [ite_eq_right hxz, star_one, mul_one]⟩
/-- **18-Qubit `Unitary (2 ^ 18)` Origin-`0` Conjugation Identity**:
For any `k : ZMod 8` and target `z : Fin (2 ^ 18)`,
`(uCoreHadamard18)⁻¹ * pointPhaseUnitary18Z8 k z * uCoreHadamard18` equals
`(pointDiagUnitary18 z)⁻¹ * ((uHadamard18)⁻¹ * pointPhaseUnitary18Z8 k 0 * uHadamard18) *
pointDiagUnitary18 z`. -/
theorem uCoreHadamard18_conj_pointPhaseUnitary18Z8_eq_origin0 (k : ZMod 8) (z : Fin (2 ^ 18))
    : (uCoreHadamard18)⁻¹ * pointPhaseUnitary18Z8 k z * uCoreHadamard18 =
    (pointDiagUnitary18 z)⁻¹ * ((uHadamard18)⁻¹ * pointPhaseUnitary18Z8 k 0 * uHadamard18) *
    pointDiagUnitary18 z := by
  apply Subtype.ext
  exact uCoreHadamard18_conj_pointPhaseDiag18_eq_origin0 (omega8 ^ k.val) z
/-!
## Section 2: `uHeadPhaseMod4Origin0` & Exact Commutation with `rElec[0]`
(`uHeadPhaseMod4Origin0_comm_rElec0`)
-/
theorem elec0_bound_in_core : 0 + 18 ≤ posCoreWires := by
  decide
theorem rest4016_bound_in_core : 18 + 4016 ≤ posCoreWires := by
  decide
/-- 18-wire register `[0 .. 18)` for Electron `0` (`rElecSlot 0`) inside `posCoreWires` (`=
  4034`). -/
def rElec0InCore : QRegister 18 posCoreWires := QRegister.block 0 18 elec0_bound_in_core
/-- 4,016-wire register `[18 .. 4034)` spanning all 217 spectator electrons `[18 .. 3924)` and
control/fine registers `[3924 .. 4034)` inside `posCoreWires`. -/
def rRest4016InCore : QRegister 4016 posCoreWires :=
  QRegister.block 18 4016 rest4016_bound_in_core
/-- `rElec0InCore` (`[0 .. 18)`) and `rRest4016InCore` (`[18 .. 4034)`) are wire-disjoint. -/
theorem rElec0InCore_disjoint_rRest4016InCore : rElec0InCore.DisjointWires rRest4016InCore :=
    disjoint_block_sep (by decide)
/-- Projects a `posCoreWires` bit assignment onto `[18 .. 4034)` by zeroing Electron `0` (`[0 ..
  18)`). -/
def zeroSlot0Bits (β : BitAssignment posCoreWires) : BitAssignment posCoreWires :=
  fun w ↦ if w.val < 18 then 0 else β w
/-- Lifts a `4016`-bit assignment on `rRest4016InCore` (`[18 .. 4034)`) to `posCoreWires` by
  setting `[0 .. 18)` to `0`. -/
def liftRest4016ToCore (γ : BitAssignment 4016) : BitAssignment posCoreWires :=
  fun w ↦
    if h : w.val < 18 then 0
    else γ ⟨w.val - 18, by have := w.isLt; dsimp [posCoreWires] at this; omega⟩
theorem liftRest4016ToCore_extract (β : BitAssignment posCoreWires) :
    liftRest4016ToCore (fun i : Fin 4016 ↦ β (rRest4016InCore i)) = zeroSlot0Bits β := by
  funext w
  dsimp only [liftRest4016ToCore, zeroSlot0Bits]
  by_cases hw : w.val < 18
  · rw [dite_eq_left hw, ite_eq_left hw]
  · rw [dite_eq_right hw, ite_eq_right hw]
    refine congrArg β (Fin.ext ?_)
    change 18 + (w.val - 18) = w.val
    omega
/-- Origin-`0` hit set on `posCoreWires`: tests whether each spectator electron `e.succ` (`1 ≤
  e.succ ≤ 217`)
is at the origin `0 : SubGridCoord64` (`slotSubGridCoord64 = fun _ ↦ 0`), and tests `e = 0` on
`zeroSlot0Bits β`
when `s0 = false`. -/
def headHitSetOrigin0Spec (β : BitAssignment posCoreWires) : Finset (Fin 218) :=
  let rCore := QRegExt.ofFin posCoreWires
  let s0 := β (wSlot0Core rCore) == 1
  Finset.univ.filter fun e : Fin 218 ↦
    (Bool.not s0 || decide (e.val ≠ 0)) &&
      decide (slotSubGridCoord64 (rElecSlot rCore e) (zeroSlot0Bits β) = fun _ ↦ 0)
/-- `ZMod 8` phase exponent of the Origin-`0` Mod-4 Head Phase Oracle on `posCoreWires`
(100% independent of Electron `0` `[0 .. 18)`!). -/
def headPhaseMod4Origin0Z8Spec (β : BitAssignment posCoreWires) : ZMod 8 :=
  let rCore := QRegExt.ofFin posCoreWires
  let β0 := zeroSlot0Bits β
  if Bool.not (headEnBoolSpec β0) then 0
  else
    let s0Z8 : ZMod 8 := if β0 (wSlot0Core rCore) == 1 then 4 else 0
    let tZ8 : ZMod 8 := if β0 (wHeadThresh rCore) == 1 then 4 else 0
    s0Z8 + ((headHitSetOrigin0Spec β0).card : ZMod 8) * (2 + tZ8)
theorem zeroSlot0Bits_idem (β : BitAssignment posCoreWires) :
    zeroSlot0Bits (zeroSlot0Bits β) = zeroSlot0Bits β := by
  funext w
  dsimp only [zeroSlot0Bits]
  split_ifs <;> rfl
theorem headPhaseMod4Origin0Z8Spec_zeroSlot0Bits (β : BitAssignment posCoreWires) :
    headPhaseMod4Origin0Z8Spec (zeroSlot0Bits β) = headPhaseMod4Origin0Z8Spec β := by
  dsimp only [headPhaseMod4Origin0Z8Spec]
  rw [zeroSlot0Bits_idem]
/-- Local wire index of `wHeadThresh` inside `rRest4016InCore` (`[18 .. 4034)`). -/
def wThInRest4016 : Wire 4016 :=
  ⟨(wHeadThresh (QRegExt.ofFin posCoreWires)).val - 18, by decide⟩
theorem rRest4016InCore_wThInRest4016 :
    rRest4016InCore wThInRest4016 = wHeadThresh (QRegExt.ofFin posCoreWires) := by
  decide
/-- `4016`-wire Origin-`0` Mod-4 Head Phase unitary on `rRest4016InCore` (`[18 .. 4034)`). -/
noncomputable def uHeadPhaseMod4Origin0Rest4016 : Unitary (2 ^ 4016) := monomialZ8UnitaryN
    wThInRest4016 (fun γ : BitAssignment 4016 ↦ headEnBoolSpec (liftRest4016ToCore γ)) (fun γ
    : BitAssignment 4016 ↦ headPhaseMod4Origin0Z8Spec (liftRest4016ToCore γ))
/-- **Origin-`0` Mod-4 Head Phase Unitary `uHeadPhaseMod4Origin0` on `posCoreWires`**:
Tests spectator electrons `1..217` against the origin `0 : Fin (2 ^ 18)` and acts purely on
`rRest4016InCore` (`[18 .. 4034)`), leaving Electron `0` (`[0 .. 18)`) completely untouched. -/
noncomputable def uHeadPhaseMod4Origin0 : Unitary (2 ^ posCoreWires) :=
  rRest4016InCore.embedUnitary uHeadPhaseMod4Origin0Rest4016
/-- `uHeadPhaseMod4Origin0` equals `monomialZ8UnitaryN (wHeadThresh _) (fun β ↦ headEnBoolSpec
  (zeroSlot0Bits β)) headPhaseMod4Origin0Z8Spec`. -/
theorem uHeadPhaseMod4Origin0_eq_monomialZ8 : uHeadPhaseMod4Origin0 = monomialZ8UnitaryN
    (wHeadThresh (QRegExt.ofFin posCoreWires)) (fun β ↦ headEnBoolSpec (zeroSlot0Bits β))
    headPhaseMod4Origin0Z8Spec := by
  dsimp only [uHeadPhaseMod4Origin0, uHeadPhaseMod4Origin0Rest4016]
  rw [embedUnitary_monomialZ8UnitaryN, rRest4016InCore_wThInRest4016]
  have hd : (fun β : BitAssignment posCoreWires ↦ headEnBoolSpec (liftRest4016ToCore (fun i ↦
      β (rRest4016InCore i)))) = (fun β ↦ headEnBoolSpec (zeroSlot0Bits β)) := by
    funext β
    rw [liftRest4016ToCore_extract]
  have hp : (fun β : BitAssignment posCoreWires ↦ headPhaseMod4Origin0Z8Spec
      (liftRest4016ToCore (fun i ↦ β (rRest4016InCore i)))) = headPhaseMod4Origin0Z8Spec := by
    funext β
    rw [liftRest4016ToCore_extract, headPhaseMod4Origin0Z8Spec_zeroSlot0Bits]
  rw [hd, hp]
theorem embedUnitary_comm_of_disjoint_local {k₁ k₂ n : ℕ} (r₁ : QRegister k₁ n)
    (r₂ : QRegister k₂ n) (hdisj : r₁.DisjointWires r₂) (U₁ : Unitary (2 ^ k₁))
    (U₂ : Unitary (2 ^ k₂)) : r₁.embedUnitary U₁ * r₂.embedUnitary U₂ = r₂.embedUnitary U₂ *
    r₁.embedUnitary U₁ := by
  apply Subtype.ext
  exact r₁.embedMatrix_comm_of_disjoint r₂ hdisj U₁.1 U₂.1
/-- **Exact Commutation of `uHeadPhaseMod4Origin0` with Electron `0`**:
Because `uHeadPhaseMod4Origin0` acts purely on `rRest4016InCore` (`[18 .. 4034)`), it commutes
with `rElec0InCore.embedUnitary U` for ANY 18-qubit unitary `U : Unitary (2 ^ 18)` on Electron `0`
(`[0 .. 18)`). -/
theorem uHeadPhaseMod4Origin0_comm_rElec0 (U : Unitary (2 ^ 18)) : rElec0InCore.embedUnitary U
    * uHeadPhaseMod4Origin0 = uHeadPhaseMod4Origin0 * rElec0InCore.embedUnitary U :=
    embedUnitary_comm_of_disjoint_local rElec0InCore rRest4016InCore
    rElec0InCore_disjoint_rRest4016InCore U uHeadPhaseMod4Origin0Rest4016
theorem rElec0InCore_disjoint_rSpectatorElec3906InCore : rElec0InCore.DisjointWires
    rSpectatorElec3906InCore := disjoint_block_sep (by decide)
theorem uSpectatorHadamard3906_comm_rElec0 (U : Unitary (2 ^ 18)) : rElec0InCore.embedUnitary
    U * uSpectatorHadamard3906 = uSpectatorHadamard3906 * rElec0InCore.embedUnitary U :=
    embedUnitary_comm_of_disjoint_local rElec0InCore rSpectatorElec3906InCore
    rElec0InCore_disjoint_rSpectatorElec3906InCore U _
theorem uSpectatorHadamard3906_inv_comm_rElec0 (U : Unitary (2 ^ 18)) :
    rElec0InCore.embedUnitary U * (uSpectatorHadamard3906)⁻¹ =
      (uSpectatorHadamard3906)⁻¹ * rElec0InCore.embedUnitary U := by
  dsimp only [uSpectatorHadamard3906]
  rw [← QRegister.embedUnitary_inv]
  exact embedUnitary_comm_of_disjoint_local rElec0InCore rSpectatorElec3906InCore
    rElec0InCore_disjoint_rSpectatorElec3906InCore U _
/-- **Exact Commutation of `(uSpectatorHadamard3906)⁻¹ * uHeadPhaseMod4Origin0 *
  uSpectatorHadamard3906` with Electron `0`**:
The Hadamard-conjugated origin-`0` head operator commutes identically with any 18-qubit unitary `U`
on Electron `0`. -/
theorem uHeadPhaseMod4Origin0ConjH_comm_rElec0 (U : Unitary (2 ^ 18)) :
    rElec0InCore.embedUnitary U * ((uSpectatorHadamard3906)⁻¹ * uHeadPhaseMod4Origin0 *
    uSpectatorHadamard3906) = ((uSpectatorHadamard3906)⁻¹ * uHeadPhaseMod4Origin0 *
    uSpectatorHadamard3906) * rElec0InCore.embedUnitary U := by
  calc rElec0InCore.embedUnitary U *
        ((uSpectatorHadamard3906)⁻¹ * uHeadPhaseMod4Origin0 * uSpectatorHadamard3906)
      = (rElec0InCore.embedUnitary U * (uSpectatorHadamard3906)⁻¹) *
          uHeadPhaseMod4Origin0 * uSpectatorHadamard3906 := by simp only [_root_.mul_assoc]
    _ = (uSpectatorHadamard3906)⁻¹ *
          (rElec0InCore.embedUnitary U * uHeadPhaseMod4Origin0) *
          uSpectatorHadamard3906 := by
          rw [uSpectatorHadamard3906_inv_comm_rElec0]; simp only [_root_.mul_assoc]
    _ = (uSpectatorHadamard3906)⁻¹ * uHeadPhaseMod4Origin0 *
          (rElec0InCore.embedUnitary U * uSpectatorHadamard3906) := by
          rw [uHeadPhaseMod4Origin0_comm_rElec0]; simp only [_root_.mul_assoc]
    _ = ((uSpectatorHadamard3906)⁻¹ * uHeadPhaseMod4Origin0 * uSpectatorHadamard3906) *
          rElec0InCore.embedUnitary U := by
          rw [uSpectatorHadamard3906_comm_rElec0]; simp only [_root_.mul_assoc]
/-!
## Section 3: 217-Electron Spectator Product Algebra (`elecProd217_mul`, `elecProd217_inv`), `0-T`
Circuit `cHad217`, and `uQft217_conj_uHeadPhaseMod4_eq_pointDiag217_conj_origin0`
-/
/-- All 217 spectator electron registers `rSpectatorSlot e` (`1 ≤ e.succ ≤ 217`) are pairwise
  wire-disjoint. -/
theorem rSpectatorSlot_disjoint {i j : Fin 217} (hij : i ≠ j) :
    (rSpectatorSlot i).DisjointWires (rSpectatorSlot j) := by
  rw [QRegister.disjoint_iff]
  intro q₁ q₂ heq
  have hval : ∀ (e : Fin 217) (q : Fin 18), (rSpectatorSlot e q).val = 18 * (e.val + 1) + q.val :=
    fun e q ↦ PosSlots24UnbarreledWide.rElecSlot_ofFin_val e.succ q
  have hv := congrArg Fin.val heq
  rw [hval i q₁, hval j q₂] at hv
  have hq1 := q₁.isLt
  have hq2 := q₂.isLt
  have hij_val : i.val = j.val := by omega
  exact hij (Fin.ext hij_val)
/-- Product homomorphism `elecProd217 A * elecProd217 B = elecProd217 (fun e ↦ A e * B e)`. -/
theorem elecProd217_mul (A B : Fin 217 → Unitary (2 ^ 18)) :
    elecProd217 A * elecProd217 B = elecProd217 (fun e ↦ A e * B e) :=
  prod_ofFn_embedUnitary_mul rSpectatorSlot (fun _ _ h ↦ rSpectatorSlot_disjoint h) A B
theorem prod_ofFn_eq_one_local {G : Type*} [Monoid G] {m : ℕ} (g : Fin m → G)
    (h : ∀ i, g i = 1) : (List.ofFn g).prod = 1 :=
  List.prod_eq_one fun x hx ↦ by
    rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
    exact h i
theorem prod_ofFn_embedUnitary_one_local {M d N : ℕ} (r : Fin M → QRegister d N) :
    (List.ofFn fun i : Fin M ↦ (r i).embedUnitary 1).prod = 1 := prod_ofFn_eq_one_local _
    (fun i ↦ QRegister.embedUnitary_one (r i))
/-- Identity law `elecProd217 (fun _ ↦ 1) = 1`. -/
theorem elecProd217_one : elecProd217 (fun _ ↦ 1) = 1 := prod_ofFn_embedUnitary_one_local
    rSpectatorSlot
theorem unitary_inv_eq_of_mul_eq_one_local {D : ℕ} {X Y : Unitary D}
    (h : Y * X = 1) : X⁻¹ = Y := by
  apply Subtype.ext
  have hval : Y.1 * X.1 = 1 := congrArg Subtype.val h
  have hX : X.1 * (X⁻¹).1 = 1 := X.2.2
  calc (X⁻¹).1 = 1 * (X⁻¹).1 := (Matrix.one_mul _).symm
    _ = (Y.1 * X.1) * (X⁻¹).1 := by rw [hval]
    _ = Y.1 * (X.1 * (X⁻¹).1) := Matrix.mul_assoc _ _ _
    _ = Y.1 := by rw [hX, Matrix.mul_one]
/-- Inverse law `(elecProd217 A)⁻¹ = elecProd217 (fun e ↦ (A e)⁻¹)`. -/
theorem elecProd217_inv (A : Fin 217 → Unitary (2 ^ 18)) :
    (elecProd217 A)⁻¹ = elecProd217 (fun e ↦ (A e)⁻¹) := by
  refine unitary_inv_eq_of_mul_eq_one_local ?_
  rw [elecProd217_mul]
  have h1 : (fun e : Fin 217 ↦ (A e)⁻¹ * A e) = fun _ ↦ 1 :=
    funext fun e ↦ Subtype.ext (A e).2.1
  rw [h1, elecProd217_one]
/-- Conjugation law `(elecProd217 U)⁻¹ * elecProd217 A * elecProd217 U = elecProd217 (fun e ↦ (U
  e)⁻¹ * A e * U e)`. -/
theorem elecProd217_conj (U A : Fin 217 → Unitary (2 ^ 18)) : (elecProd217 U)⁻¹ * elecProd217
    A * elecProd217 U = elecProd217 (fun e ↦ (U e)⁻¹ * A e * U e) := by
  rw [elecProd217_inv, elecProd217_mul, elecProd217_mul]
/-- 217-electron Mod-4 point-phase unitary applying `pointPhaseUnitary18Z8 k z` to each spectator
  slot `1 .. 217`. -/
noncomputable def uSpectatorPhase217 (k : ZMod 8) (z : Fin (2 ^ 18)) : Unitary (2 ^ posCoreWires) :=
  elecProd217 (fun _ ↦ pointPhaseUnitary18Z8 k z)
/-- **217-Electron Origin-`0` Point-QFT Conjugation Theorem**:
For any `k : ZMod 8` and any 18-bit target coordinate `z : Fin (2 ^ 18)`, conjugating
`uSpectatorPhase217 k z` by `uQft217` (`∏ e ∈ 1..217, uCoreHadamard18_e`) is **identically equal**
to conjugating the **origin-`0`** operator `(uHad217)⁻¹ * uSpectatorPhase217 k 0 * uHad217`
by `pointDiag217 z`! -/
theorem uQft217_conj_uSpectatorPhase217_eq_pointDiag217_conj_origin0 (k : ZMod 8)
    (z : Fin (2 ^ 18)) : (uQft217)⁻¹ * uSpectatorPhase217 k z * uQft217 = (pointDiag217 z)⁻¹ *
    ((uHad217)⁻¹ * uSpectatorPhase217 k 0 * uHad217) * pointDiag217 z := by
  dsimp only [uQft217, uHad217, pointDiag217, uSpectatorPhase217]
  rw [elecProd217_conj, elecProd217_conj, elecProd217_conj]
  refine congrArg elecProd217 (funext fun _ ↦ ?_)
  exact uCoreHadamard18_conj_pointPhaseUnitary18Z8_eq_origin0 k z
/-- Concrete 6-wire Hadamard circuit `cHadamard6 : Circuit 6` (`0 T`, `0 TOFF`) with
  `cHadamard6.eval = uHadamard6`. -/
def cHadamard6 : Circuit 6 :=
  Circuit.H 5 ;;ᶜ Circuit.H 4 ;;ᶜ Circuit.H 3 ;;ᶜ
    Circuit.H 2 ;;ᶜ Circuit.H 1 ;;ᶜ Circuit.H 0
theorem cHadamard6_eval : cHadamard6.eval = uHadamard6 := by
  dsimp only [cHadamard6, uHadamard6, wireHadamard6, Circuit.H, Circuit.single]
  simp only [Circuit.eval_seq, Circuit.eval_gate, PrimitiveGate.eval, _root_.mul_assoc]
@[simp] theorem cHadamard6_count_T : cHadamard6.count PrimitiveGate.T = 0 := rfl
@[simp] theorem cHadamard6_count_TOFF : cHadamard6.count TOFF = 0 := rfl
/-- Concrete 18-wire Hadamard circuit `cHadamard18 : Circuit 18` (`0 T`, `0 TOFF`) with
  `cHadamard18.eval = uHadamard18`. -/
def cHadamard18 : Circuit 18 :=
  (cHadamard6.onRegister (QRegister.block 12 6 (by decide))) ;;ᶜ
    (cHadamard6.onRegister (QRegister.block 6 6 (by decide))) ;;ᶜ
    (cHadamard6.onRegister (QRegister.block 0 6 (by decide)))
theorem cHadamard18_eval : cHadamard18.eval = uHadamard18 := by
  dsimp only [cHadamard18, uHadamard18]
  simp only [Circuit.eval_seq, Circuit.eval_onRegister, cHadamard6_eval, _root_.mul_assoc]
@[simp] theorem cHadamard18_count_T : cHadamard18.count PrimitiveGate.T = 0 := rfl
@[simp] theorem cHadamard18_count_TOFF : cHadamard18.count TOFF = 0 := rfl
/-- Right-to-left circuit sequencing `seqRevList` so `(seqRevList L).eval = (L.map
  Circuit.eval).prod`. -/
def seqRevList {n : ℕ} : List (Circuit n) → Circuit n
  | [] => .identity
  | c :: cs => Circuit.seq (seqRevList cs) c
theorem seqRevList_eval {n : ℕ} :
    ∀ L : List (Circuit n), (seqRevList L).eval = (L.map Circuit.eval).prod
  | [] => rfl
  | c :: cs => by
      simp only [seqRevList, Circuit.eval_seq, seqRevList_eval cs, List.map_cons, List.prod_cons]
theorem seqRevList_count {n a : ℕ} (g : PrimitiveGate a) :
    ∀ L : List (Circuit n), (seqRevList L).count g = (L.map (Circuit.count g)).sum
  | [] => rfl
  | c :: cs => by
      simp only [seqRevList, Circuit.count_seq, seqRevList_count g cs,
        List.map_cons, List.sum_cons, Nat.add_comm]
theorem embedUnitary_list_prod {k n : ℕ} (r : QRegister k n) :
    ∀ L : List (Unitary (2 ^ k)), (L.map r.embedUnitary).prod = r.embedUnitary L.prod
  | [] => (QRegister.embedUnitary_one r).symm
  | u :: us => by
      simp only [List.map_cons, List.prod_cons, embedUnitary_list_prod r us,
        ← QRegister.embedUnitary_mul]
/-- Concrete `0-T`, `0-TOFF` circuit `cHad217 rCore` applying `cHadamard18` to each of the `217`
spectator electron slots `1 .. 217` and evaluating to `rCore.embedUnitary uHad217`. -/
def cHad217 {n : ℕ} (rCore : QRegister posCoreWires n) : Circuit n :=
  seqRevList (List.ofFn fun e : Fin 217 ↦ cHadamard18.onRegister (rCore.compose (rSpectatorSlot e)))
def cHad217Inv {n : ℕ} (rCore : QRegister posCoreWires n) : Circuit n :=
  (cHad217 rCore).inverse
@[simp] theorem cHad217_count_T {n : ℕ} (rCore : QRegister posCoreWires n) :
    (cHad217 rCore).count PrimitiveGate.T = 0 := by
  dsimp only [cHad217]
  rw [seqRevList_count]
  simp
@[simp] theorem cHad217_count_TOFF {n : ℕ} (rCore : QRegister posCoreWires n) :
    (cHad217 rCore).count TOFF = 0 := by
  dsimp only [cHad217]
  rw [seqRevList_count]
  simp
@[simp] theorem cHad217Inv_count_T {n : ℕ} (rCore : QRegister posCoreWires n) :
    (cHad217Inv rCore).count PrimitiveGate.T = 0 := by
  dsimp only [cHad217Inv]
  rw [Circuit.count_inverse_of_ne PrimitiveGate.T (by decide) (by decide), cHad217_count_T]
@[simp] theorem cHad217Inv_count_TOFF {n : ℕ} (rCore : QRegister posCoreWires n) :
    (cHad217Inv rCore).count TOFF = 0 := by
  dsimp only [cHad217Inv]
  rw [Circuit.count_inverse_of_ne TOFF (by decide) (by decide), cHad217_count_TOFF]
theorem cHad217_eval {n : ℕ} (rCore : QRegister posCoreWires n) :
    (cHad217 rCore).eval = rCore.embedUnitary uHad217 := by
  dsimp only [cHad217, uHad217, elecProd217]
  rw [seqRevList_eval, ← embedUnitary_list_prod rCore, List.map_ofFn, List.map_ofFn]
  refine congrArg List.prod (congrArg List.ofFn (funext fun e ↦ ?_))
  dsimp only [Function.comp_def]
  rw [Circuit.eval_onRegister, cHadamard18_eval, QRegister.embedUnitary_compose]
theorem cHad217Inv_eval {n : ℕ} (rCore : QRegister posCoreWires n) :
    (cHad217Inv rCore).eval = rCore.embedUnitary (uHad217)⁻¹ := by
  dsimp only [cHad217Inv]
  rw [Circuit.eval_inverse, cHad217_eval, QRegister.embedUnitary_inv]
end OriginZeroHeadMod4Reduction
/-!
# Stage-A Origin-`0` Mod-4 Head Circuits & Full 218-Electron Conjugation Closure
Completes the Stage-A Origin-`0` Mod-4 Head Phase circuit synthesis and 218-electron QFT
conjugation bridge (`TOFF = 0`):
1. **Section 1 — Streamlined `15,190-T` (`19`-Wire) Origin-`0` 217-Spectator Mod-4 Accumulator
Circuit
   `dSpectatorStreamOrigin0_19Dyn` & `15,258-T` Frame Bound (`-289 T/call = -578 T/step`)**:
   - Because `uHeadPhaseMod4Origin0` tests every spectator electron `e ∈ 1..217` against the fixed
   origin
     `0 : Fin (2 ^ 18)` (`all 18 bits zero`) instead of `yTarget = y_0 - q`, it requires **zero
     3-axis
     6-bit carry/mux steps** (`-144 T`, `-36` scratch wires) and **zero `cShift` CNOT broadcasts**!
   - Constructs `dSpectatorStreamOrigin0_19Dyn` (`19` scratch wires, `217 * 70 = 15,190 T`, `TOFF =
   0`)
     and its Hadamard-conjugated wrapper `dSpectatorStreamOrigin0ConjH_19Dyn` (`15,190 T`, `TOFF =
     0`),
     and proves `dSpectatorStreamOrigin0_19Dyn_realizesSub17` (`RealizesCleanUnitary`).
2. **Section 2 — Turnkey Origin-`0` Hadamard-Conjugated Head Circuits
(`dHeadPhaseMod4Origin0ConjH_254`,
   `dHeadPhaseMod4Origin0PostSwapConjH_107`, `dHeadPhaseMod4Origin0PostSwapConjH_172`,
   `dHeadPhaseMod4Origin0PostSwapConjH_178`)**:
   - Defines the `0-T` virtual zero-slot-`0` core register `rCoreZero0 rCore rZero18 hCZ`
   (substituting a
     clean `|0^{18}⟩` slice `rZero18` for Electron `0` `[0 .. 18)` at `0` Clifford gates and `0`
     `T` gates)
     and proves `cSpectatorHadamard3906_rCoreZero0_eq : cSpectatorHadamard3906 (rCoreZero0 rCore
     rZero18 hCZ) = cSpectatorHadamard3906 rCore`.
   - Constructs `dHeadPhaseMod4Origin0ConjH_254` (`≤ 15,476 T`, `TOFF = 0`),
     `dHeadPhaseMod4Origin0PostSwapConjH_107` (`107 ≤ mScr`, `15,547 T`, `TOFF = 0`),
     `dHeadPhaseMod4Origin0PostSwapConjH_172` (`172 ≤ mScr`, `15,547 T`, `TOFF = 0`), and
     `dHeadPhaseMod4Origin0PostSwapConjH_178` (`178 ≤ mScr`, `15,547 T`, `TOFF = 0`), with their
     exact
     `.count TOFF = 0`, `.count .T`, and `RealizesEmbeddedUnitaryWithCleanWorkspace` theorems.
3. **Section 3 — Complete 218-Electron Conjugation Theorem
`fullQft218_conj_uHeadPhaseMod4_eq_stageA_origin0`
   & Electron-`0` Commutation Cancellation (`uQft0_conj_pointDiag217_conj_origin0_eq`)**:
   - Defines `uQft0 := rElec0InCore.embedUnitary uCoreHadamard18` and `fullQft218 := uQft0 *
   uQft217`,
     and proves `uQft0_comm_elecProd217`, `uQft0_comm_uQft217`, and
     `fullQft218_conj_eq_uQft0_conj_uQft217_conj`.
   - Proves **`fullQft218_conj_uSpectatorPhase217_eq_stageA_origin0`** and
     **`fullQft218_conj_uHeadPhaseMod4_eq_stageA_origin0`**:
     $$\bigl(uQft0 \cdot uQft217\bigr)^{-1} \cdot \text{uHeadPhaseMod4} \cdot \bigl(uQft0 \cdot
     uQft217\bigr)
       = uQft0^{-1} \cdot \bigl((pointDiag217\, z)^{-1} \cdot \bigl((uHad217)^{-1} \cdot
       \text{uHeadPhaseMod4Origin0} \cdot uHad217\bigr) \cdot pointDiag217\, z\bigr) \cdot uQft0.$$
   - Proves **`uQft0_conj_uHeadPhaseMod4Origin0ConjH_eq`** and
   **`uQft0_conj_pointDiag217_conj_origin0_eq`**:
     because `uQft0` commutes with `(uSpectatorHadamard3906)⁻¹ * uHeadPhaseMod4Origin0 *
     uSpectatorHadamard3906`,
     `uQft0` cancels identically on the middle origin-`0` operator!
-/
namespace OriginZeroHeadMod4Circuit14900
open PosSlots24BranchConcrete (posCoreWires)
open DyadicQft64WalkCircuit (list_prod_comm_of_all)
open StageAPosHeadConjugatedCircuit (uCoreHadamard18 rSpectatorSlot elecProd217
  uQft217)
open OriginZeroHeadMod4Reduction (rElec0InCore
  embedUnitary_comm_of_disjoint_local)
/- Electron-`0` embedded 18-qubit QFT unitary `rElec0InCore.embedUnitary uCoreHadamard18` on
`posCoreWires`. -/
open HermitianMat SpecsAux SpecsAux.SpecMirror
open scoped ComplexOrder MatrixOrder Circuit.Notation
noncomputable def uQft0 : Unitary (2 ^ posCoreWires) :=
  rElec0InCore.embedUnitary uCoreHadamard18
/-- Full 218-electron QFT unitary `uQft0 * uQft217` on `posCoreWires`. -/
noncomputable def fullQft218 : Unitary (2 ^ posCoreWires) := uQft0 * uQft217
/-- Electron `0` (`rElec0InCore`, `[0 .. 18)`) is wire-disjoint from every spectator electron
register `rSpectatorSlot e` (`[18 .. 3924)`). -/
theorem rElec0InCore_disjoint_rSpectatorSlot (e : Fin 217) :
    rElec0InCore.DisjointWires (rSpectatorSlot e) := by
  rw [QRegister.disjoint_iff]
  intro q₀ qₑ heq
  have hv0 : (rElec0InCore q₀).val = q₀.val := Nat.zero_add q₀.val
  have hve : (rSpectatorSlot e qₑ).val = 18 * (e.val + 1) + qₑ.val :=
    PosSlots24UnbarreledWide.rElecSlot_ofFin_val e.succ qₑ
  have hv := congrArg Fin.val heq
  rw [hv0, hve] at hv
  have hq0 := q₀.isLt
  omega
/-- Any unitary `rElec0InCore.embedUnitary U₀` on Electron `0` commutes with any 217-spectator
  product `elecProd217 A`. -/
theorem embed_rElec0InCore_comm_elecProd217 (U₀ : Unitary (2 ^ 18))
    (A : Fin 217 → Unitary (2 ^ 18)) : rElec0InCore.embedUnitary U₀ * elecProd217 A =
    elecProd217 A * rElec0InCore.embedUnitary U₀ := by
  symm
  unfold elecProd217
  refine list_prod_comm_of_all _ (rElec0InCore.embedUnitary U₀) fun x hx ↦ ?_
  rcases List.mem_ofFn.mp hx with ⟨e, rfl⟩
  exact (embedUnitary_comm_of_disjoint_local rElec0InCore (rSpectatorSlot e)
    (rElec0InCore_disjoint_rSpectatorSlot e) U₀ (A e)).symm
/-- `uQft0` commutes with `uQft217`. -/
theorem uQft0_comm_uQft217 : uQft0 * uQft217 = uQft217 * uQft0 :=
  embed_rElec0InCore_comm_elecProd217 uCoreHadamard18 (fun _ ↦ uCoreHadamard18)
theorem unitary_mul_inv_rev_local {D : ℕ} (A B : Unitary D) : (A * B)⁻¹ = B⁻¹ * A⁻¹ := by
  apply Subtype.ext
  exact star_mul A.1 B.1
/-- **218-Electron Conjugation Split (`fullQft218_conj_eq_uQft0_conj_uQft217_conj`)**:
Because `uQft0` and `uQft217` commute, conjugating any `U : Unitary (2 ^ posCoreWires)` by
`fullQft218 = uQft0 * uQft217` equals conjugating `U` first by `uQft217` and then by `uQft0`. -/
theorem fullQft218_conj_eq_uQft0_conj_uQft217_conj (U : Unitary (2 ^ posCoreWires)) :
    (uQft0 * uQft217)⁻¹ * U * (uQft0 * uQft217) =
      uQft0⁻¹ * (uQft217⁻¹ * U * uQft217) * uQft0 := by
  have h1 : (uQft0 * uQft217)⁻¹ = uQft0⁻¹ * uQft217⁻¹ := by
    rw [uQft0_comm_uQft217, unitary_mul_inv_rev_local]
  rw [h1]
  conv_lhs => rw [uQft0_comm_uQft217]
  simp only [_root_.mul_assoc]
end OriginZeroHeadMod4Circuit14900
end SharedScope
end SlimStageADepsB

noncomputable section BoothOpt_StageBPartnerCoreShave
set_option maxRecDepth 20000

section
namespace BoothOpt_StageBPartnerCoreShave
set_option backward.isDefEq.respectTransparency false
set_option exponentiation.threshold 256
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open SpecsAux SpecsAux.SpecMirror
open Dyadic128CoulombMath
open PosSlots24BranchConcrete
open StreamingBchComparator
open PosSlots24CompactPhase288
open PosSlots24SemanticBridge
open PosSlots24SpectatorPrunedPhase
open PosSlots24SpectatorPrunedPhase.MidK6Sub252
open MultiBankWStateRouter
open MidKickSub33 MidK6Sub126
open OrbitSandPacked18
open MidKickOpt MidK6UnbufOpt
open OrbitSandPacked12
open OrbitSandPacked13
open PosSlots24Barrel3Pass
open AnchorSwap0Split133
open ParticleOneHotWState
open scoped Matrix ComplexOrder MatrixOrder BigOperators Circuit.Notation
open scoped Matrix.Norms.L2Operator
section Part1_OrbitSandBoothOpt
set_option maxRecDepth 16384
local instance (priority := 1000000) instNeZeroTwoPowBoothOptAux (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
local instance (priority := 1000000) instNeZero143BoothOpt : NeZero 143 := ⟨by decide⟩
local instance (priority := 1000000) instNeZero162BoothOpt : NeZero 162 := ⟨by decide⟩
open PrimitiveGate (TOFF T)
open OctahedralOrbit hiding ket writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem eval_seq_mulVec
open MeasureBranchHadamardSem (ket eval_seq_mulVec projZeroAll
  projZeroAll_conjTranspose)
open MomSlot0CircuitHalf (writeReg writeReg_apply_reg
  writeReg_apply_of_not_mem)
open BchCubeDecoder hiding ket_diagonalSignUnitaryN
open PosSlots24PartnerMuxZeroT123 hiding sandPhase18
open PosSlots24PartnerMux288 (rawOrbitCoord128 sandPhase18)
open PosSlots24OrbitToggleFast288 hiding ite_pos ite_neg dite_pos
  dite_neg rawOrbitCoord128 orbitRankFin16 matrix_ext_ket basisBits_symm_apply_at
open PosTailWithAnchor18_244 (ctxSupportsBelowB S_cleanCtxPred
  p2t_realizes_toDynWithDyn_of_validPred constClean_toDynWithDyn_perm)
open OrbitSandHeldMidK6Sub (tempCtx_append_assoc
  toDynWithDyn_count_toff_eq)
open Guard_StageBK6OrbitSandShave (midK6GuardBaseT
  dMidK6GuardOptDyn count_dMidK6GuardOptDyn_toff count_dMidK6GuardOptDyn_t_le_exact
  dMidK6GuardOptDyn_realizes)
/-- `18`-AND linear-AND step table for `triNum(v) = v(v+1)/2` on `0 ≤ v ≤ 64` (`-2` ANDs vs
  `triSteps20ListB10`). -/
def triSteps18List : List (ℕ × ℕ) := [
  (18, 15), (12, 137), (401, 414), (657, 6), (778, 274), (1424, 2433),
  (4, 6659), (5402, 7194), (18456, 8328), (8327, 18049), (2816, 68883), (8196, 103321),
  (32, 3089), (32, 6928), (32, 153998), (32, 360347), (32, 99849), (32, 262160)
]
/-- `12`-bit output parity masks for `triSteps18List`. -/
def triOuts12_18 (j : Fin 12) : ℕ :=
  match j.val with
  | 0 => 3
  | 1 => 6
  | 2 => 1034
  | 3 => 646
  | 4 => 3120
  | 5 => 532178
  | 6 => 1234816
  | 7 => 2467337
  | 8 => 4556313
  | 9 => 8388640
  | 10 => 16777216
  | _ => 64
set_option maxRecDepth 20000 in
theorem triLut18_bool_val :
    ∀ v : Fin 65,
      let acc := evalLinAndBool triSteps18List (inBool7 v.val)
      packBoolFn (fun j : Fin 12 ↦ maskXorBool (triOuts12_18 j) acc) = triNum v.val := by
  decide
theorem v7List143_lt34 : ∀ w ∈ v7List143, w.val < 34 :=
  fun w hw ↦ lt_trans (v7List143_lt32 w hw) (by decide)
/-- `61`-`TempAnd` (`244 T`) `triNum v + tetNum w` context placing `triSteps18List` at `base = 34`
so `tri12W143 j = 54 + j` is preserved (`-2` `TempAnd`s = `-8 T` per tail vs `vwLutAdd143`). -/
def vwLutAddOpt143 : TempCtx 143 :=
  let s3a := ctxLinAndLut 12 34 v7List143 triSteps18List triOuts12_18 (by decide) v7List143_lt34
  let s3b := ctxLinAndLut 16 66 w7List143 tetSteps29List tetOuts16 (by decide) w7List143_lt66
  let s3c :=
    ctxAddMod2Pow 14 114 (by decide) triPad15Hi143 tet15HiW143 cinZero143
      (fun i j ↦ wire_ne_of_lt (lt_of_le_of_lt (triPad15Hi143_le65 i)
        (by have := j.isLt; dsimp [tet15HiW143, tet16W143]; omega)))
      (fun i ↦ wire_ne_of_lt (lt_of_le_of_lt (triPad15Hi143_le65 i) (by decide)))
      (fun i ↦ wire_ne_of_lt (by have := i.isLt; dsimp [tet15HiW143, tet16W143, cinZero143]; omega))
      (fun i ↦ lt_of_le_of_lt (triPad15Hi143_le65 i) (by decide))
      (fun i ↦ by have := i.isLt; dsimp [tet15HiW143, tet16W143]; omega)
      (by decide)
  s3a.append (s3b.append s3c)
theorem vwLutAddOpt143_supp128B : ctxSupportsBelowB 128 vwLutAddOpt143 = true := rfl
theorem vwLutAddOpt143_disj_supp : vwLutAddOpt143.DisjointFrom mutOrb143 ∧
    vwLutAddOpt143.SupportsBelowCtx 128 := by
  have hd3a := ctxLinAndLut_disj (mutW := mutOrb143) 12 34 v7List143
    triSteps18List triOuts12_18 (by decide) v7List143_lt34 v7List143_not_mut
    (fun _ hw ↦ not_mutOrb143_of_ge28 (by omega))
  have hd3b := ctxLinAndLut_disj (mutW := mutOrb143) 16 66 w7List143
    tetSteps29List tetOuts16 (by decide) w7List143_lt66 w7List143_not_mut
    (fun _ hw ↦ not_mutOrb143_of_ge28 (by omega))
  obtain ⟨hdAdd, _⟩ := ctxAddMod2Pow_disj_supp (mutW := mutOrb143) 14 114 (by decide)
    triPad15Hi143 tet15HiW143 cinZero143 _ _ _ _ _ _
    triPad15Hi143_not_mut
    (fun i ↦ not_mutOrb143_of_ge28 (by dsimp [tet15HiW143, tet16W143]; omega))
    (not_mutOrb143_of_ge28 (by decide))
    (fun _ hw ↦ not_mutOrb143_of_ge28 (by omega))
  exact ⟨TempCtx.disjointFrom_append hd3a (TempCtx.disjointFrom_append hd3b hdAdd),
    supportsBelowCtx_of_ctxSupportsBelowB vwLutAddOpt143_supp128B⟩
/-- `64`-`TempAnd` (`256 T`) Packed-12 tail context (`ctxUnpack12_143` + `vwLutAddOpt143`). -/
def vwTail12OptCtx143 : TempCtx 143 := ctxUnpack12_143.append vwLutAddOpt143
theorem vwTail12OptCtx143_countTempAnd : vwTail12OptCtx143.countTempAnd = 64 := rfl
theorem vwTail12OptCtx143_supp128B : ctxSupportsBelowB 128 vwTail12OptCtx143 = true := rfl
theorem vwTail12OptCtx143_disj_supp : vwTail12OptCtx143.DisjointFrom mutOrb143 ∧
    vwTail12OptCtx143.SupportsBelowCtx 128 := ⟨TempCtx.disjointFrom_append
    ctxUnpack12_143_disj_supp.1 vwLutAddOpt143_disj_supp.1,
    supportsBelowCtx_of_ctxSupportsBelowB vwTail12OptCtx143_supp128B⟩
section IrredTailOpt143
theorem vwLutAddOpt143_block (q₀ : Wire 143) : ∃ sTail : BitAssignment 143 → BitAssignment
    143, ScopedBlock 143 (143 - 32) sTail (.z q₀) (vwLutAddOpt143.plug (.z q₀)) ∧ ∀
    (β₆ : BitAssignment 143) (canon : CanonicalTriple65), cleanRem 143 (143 - 32) β₆ → β₆
    wZero143 = 0 → bitsVal (fun k ↦ β₆ (v7W143 k)) = canon.v.val → bitsVal
    (fun k ↦ β₆ (w7W143 k)) = canon.w.val → (∀ k : Fin 16, sTail β₆ (outVW16_143 k) =
    basisBits 16 (outVWVal canon) k) ∧ sTail β₆ (tet16W143 0) = tetBit0 canon := by
  let s3a := ctxLinAndLut 12 34 v7List143 triSteps18List triOuts12_18 (by decide) v7List143_lt34
  let s3b := ctxLinAndLut 16 66 w7List143 tetSteps29List tetOuts16 (by decide) w7List143_lt66
  let s3c :=
    ctxAddMod2Pow 14 114 (by decide) triPad15Hi143 tet15HiW143 cinZero143
      (fun i j ↦ wire_ne_of_lt (lt_of_le_of_lt (triPad15Hi143_le65 i)
        (by have := j.isLt; dsimp [tet15HiW143, tet16W143]; omega)))
      (fun i ↦ wire_ne_of_lt (lt_of_le_of_lt (triPad15Hi143_le65 i) (by decide)))
      (fun i ↦ wire_ne_of_lt (by have := i.isLt; dsimp [tet15HiW143, tet16W143, cinZero143]; omega))
      (fun i ↦ lt_of_le_of_lt (triPad15Hi143_le65 i) (by decide))
      (fun i ↦ by have := i.isLt; dsimp [tet15HiW143, tet16W143]; omega)
      (by decide)
  have hLeaf0 : ScopedBlock 143 (143 - 128) id (.z q₀) (.z q₀) :=
    ⟨trivial, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  obtain ⟨sAdd, hAdd_0, hSpecAdd⟩ := ScopedBlock.ctxAddMod2Pow_block (M := 143)
    14 114 (by decide) triPad15Hi143 tet15HiW143 cinZero143
    (fun i j ↦ wire_ne_of_lt (lt_of_le_of_lt (triPad15Hi143_le65 i)
      (by have := j.isLt; dsimp [tet15HiW143, tet16W143]; omega)))
    (fun i ↦ wire_ne_of_lt (lt_of_le_of_lt (triPad15Hi143_le65 i) (by decide)))
    (fun i ↦ wire_ne_of_lt (by have := i.isLt; dsimp [tet15HiW143, tet16W143, cinZero143]; omega))
    tet15HiW143_injective
    (fun i ↦ lt_of_le_of_lt (triPad15Hi143_le65 i) (by decide))
    (fun i ↦ by have := i.isLt; dsimp [tet15HiW143, tet16W143]; omega)
    (by decide)
    (.z q₀) (.z q₀) id hLeaf0
  have hAdd : ScopedBlock 143 (143 - 113) sAdd (.z q₀) (s3c.plug (.z q₀)) :=
      ⟨pkValidCleanRemUp (by decide) hAdd_0.valid, fun β hβ ↦ hAdd_0.bits β (fun u hu ↦ hβ u
      (by omega)), fun β hβ ↦ hAdd_0.sign β (fun u hu ↦ hβ u (by omega))⟩
  obtain ⟨sLut2, hLut2, hSpecLut2⟩ := ScopedBlock.ctxLinAndLut_block (M := 143)
    16 66 w7List143 tetSteps29List tetOuts16 (by decide) w7List143_lt66
    (.z q₀) (s3c.plug (.z q₀)) sAdd hAdd
  obtain ⟨sLut1, hLut1, hSpecLut1⟩ := ScopedBlock.ctxLinAndLut_block (M := 143)
    12 34 v7List143 triSteps18List triOuts12_18 (by decide) v7List143_lt34
    (.z q₀) (s3b.plug (s3c.plug (.z q₀))) (fun β ↦ sAdd (sLut2 β)) hLut2
  have hLut1_32 : ScopedBlock 143 (143 - 32) (fun β ↦ sAdd (sLut2 (sLut1 β))) (.z q₀)
      (s3a.plug (s3b.plug (s3c.plug (.z q₀)))) := ⟨pkValidCleanRemUp (by decide) hLut1.valid,
      fun β hβ ↦ hLut1.bits β (fun u hu ↦ hβ u (by omega)), fun β hβ ↦ hLut1.sign β (fun u hu
      ↦ hβ u (by omega))⟩
  have hFull : ScopedBlock 143 (143 - 32) (fun β ↦ sAdd (sLut2 (sLut1 β))) (.z q₀)
      (vwLutAddOpt143.plug (.z q₀)) := by
    dsimp only [vwLutAddOpt143]
    rw [TempCtx.append_plug, TempCtx.append_plug]
    exact hLut1_32
  refine ⟨fun β ↦ sAdd (sLut2 (sLut1 β)), hFull, fun β₆ canon hcl6 hβ₆_z0 hv_val hw_val ↦ ?_⟩
  have hv_bb : (fun k : Fin 7 ↦ β₆ (v7W143 k)) =
      basisBits 7 ⟨canon.v.val, lt_trans canon.v.isLt (by decide)⟩ :=
    (bits_eq_basisBits_of_val _).trans (congrArg (basisBits 7) (Fin.ext hv_val))
  have hw_bb : (fun k : Fin 7 ↦ β₆ (w7W143 k)) =
      basisBits 7 ⟨canon.w.val, lt_trans canon.w.isLt (by decide)⟩ :=
    (bits_eq_basisBits_of_val _).trans (congrArg (basisBits 7) (Fin.ext hw_val))
  let β₇ := sLut1 β₆
  obtain ⟨hcl7, hkeep7, hbits7⟩ := hSpecLut1 β₆ (fun u hu ↦ hcl6 u (by omega))
  have hv7_map : v7List143.map β₆ = (inBool7 canon.v.val).map b2z := by
    rw [inBool7_map_b2z canon.v]
    dsimp only [v7List143, List.map]
    simp only [congrFun hv_bb]
  have htri_val7 : bitsVal (fun j : Fin 12 ↦ β₇ (tri12W143 j)) = triNum canon.v.val := by
    have hfn : (fun j : Fin 12 ↦ β₇ (tri12W143 j)) = fun j : Fin 12 ↦ b2z (maskXorBool
        (triOuts12_18 j) (evalLinAndBool triSteps18List (inBool7 canon.v.val))) := by
      funext j
      have hj_eq : tri12W143 j = ⟨34 + 2 + triSteps18List.length + j.val, by
          have := j.isLt; dsimp [triSteps18List]; omega⟩ := rfl
      dsimp only [β₇]
      rw [hj_eq, hbits7 j, hv7_map, ← map_b2z_evalLinAndBool, ← b2z_maskXorBool]
    rw [hfn, bitsVal_b2z_eq_packBoolFn]
    exact triLut18_bool_val canon.v
  let β₈ := sLut2 β₇
  obtain ⟨hcl8, hkeep8, hbits8⟩ := hSpecLut2 β₇ hcl7
  have hw7_map : w7List143.map β₇ = (inBool7 canon.w.val).map b2z := by
    have hmap76 : w7List143.map β₇ = w7List143.map β₆ :=
      list_map_eq_of_forall fun u hu ↦ by
        have hlt : u.val < 34 := by
          simp only [w7List143, List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        exact hkeep7 u hlt
    rw [hmap76, inBool7_map_b2z canon.w]
    dsimp only [w7List143, List.map]
    simp only [congrFun hw_bb]
  have htet_val8 : bitsVal (fun j : Fin 16 ↦ β₈ (tet16W143 j)) = tetNum canon.w.val := by
    have hfn : (fun j : Fin 16 ↦ β₈ (tet16W143 j)) = fun j : Fin 16 ↦ b2z (maskXorBool
        (tetOuts16 j) (evalLinAndBool tetSteps29List (inBool7 canon.w.val))) := by
      funext j
      have hj_eq : tet16W143 j = ⟨66 + 2 + tetSteps29List.length + j.val, by
          have := j.isLt; dsimp [tetSteps29List]; omega⟩ := rfl
      dsimp only [β₈]
      rw [hj_eq, hbits8 j, hw7_map, ← map_b2z_evalLinAndBool, ← b2z_maskXorBool]
    rw [hfn, bitsVal_b2z_eq_packBoolFn]
    exact tetLut29_bool_val canon.w
  have htet_bb8 : (fun j : Fin 16 ↦ β₈ (tet16W143 j)) =
      basisBits 16 ⟨tetNum canon.w.val, by
        have := (tetRank65 canon).isLt
        have hp : (tetRank65 canon).val = tetNum canon.w.val + triNum canon.v.val + canon.u.val :=
            rfl
        dsimp [orbitCount47905] at this; omega⟩ :=
    (bits_eq_basisBits_of_val _).trans (congrArg (basisBits 16) (Fin.ext htet_val8))
  have hβ₈_z0 : β₈ wZero143 = 0 :=
    (hkeep8 wZero143 (by decide)).trans ((hkeep7 wZero143 (by decide)).trans hβ₆_z0)
  have htri_keep8 : ∀ j : Fin 12, β₈ (tri12W143 j) = β₇ (tri12W143 j) :=
    fun j ↦ hkeep8 _ (by have := j.isLt; dsimp [tri12W143]; omega)
  have htriPadHi_val8 : bitsVal (fun j : Fin 15 ↦ β₈ (triPad15Hi143 j)) =
      bitsVal (fun j : Fin 11 ↦ β₇ (tri12W143 j.succ)) := by
    let f11 : Fin 11 → ZMod 2 := fun j ↦ β₇ (tri12W143 j.succ)
    have hfn : (fun j : Fin (11 + 4) ↦ β₈ (triPad15Hi143 j)) =
        fun j : Fin (11 + 4) ↦ if hj : j.val < 11 then f11 ⟨j.val, hj⟩ else 0 := by
      funext j
      dsimp only [triPad15Hi143, f11]
      split_ifs with hj
      · exact htri_keep8 ⟨j.val + 1, by omega⟩
      · exact hβ₈_z0
    change bitsVal (fun j : Fin (11 + 4) ↦ β₈ (triPad15Hi143 j)) = bitsVal f11
    rw [hfn]
    exact bitsVal_padZeroRight (W := 11) (K := 4) f11
  let β₉ := sAdd β₈
  have hcin : β₈ cinZero143 = 0 := hcl8 cinZero143 (by decide)
  obtain ⟨_, hkeep9, hval9⟩ := hSpecAdd β₈ (fun u hu ↦ hcl8 u (by dsimp [tetSteps29List]; omega))
  have htri0_keep9 : β₉ (tri12W143 0) = β₇ (tri12W143 0) :=
    (hkeep9 (tri12W143 0) (by decide)
      (fun j ↦ wire_ne_of_lt (by
          have := j.isLt; dsimp [tri12W143, tet15HiW143, tet16W143]; omega))).trans
      (htri_keep8 0)
  have htet0_keep9 : β₉ (tet16W143 0) = tetBit0 canon :=
    (hkeep9 (tet16W143 0) (by decide)
      (fun j ↦ wire_ne_of_lt (by have := j.isLt; dsimp [tet15HiW143, tet16W143]; omega))).trans
      (congrFun htet_bb8 0)
  have hout_succ : (fun j : Fin 15 ↦ β₉ (outVW16_143 j.succ)) =
      fun j : Fin 15 ↦ β₉ (tet15HiW143 j) := by
    funext j; dsimp [outVW16_143, tet15HiW143]
  have hout0 : β₉ (outVW16_143 0) = β₇ (tri12W143 0) := htri0_keep9
  have hout_val : bitsVal (fun k : Fin 16 ↦ β₉ (outVW16_143 k)) = (outVWVal canon).val := by
    rw [bitsVal_succ_split, hout0, hout_succ]
    dsimp only [β₉, outVWVal]
    rw [hval9, htriPadHi_val8, hcin]
    have hsplit_tri7 := bitsVal_succ_split (fun j : Fin 12 ↦ β₇ (tri12W143 j))
    have hsplit_tet8 := bitsVal_succ_split (fun j : Fin 16 ↦ β₈ (tet16W143 j))
    rw [htri_val7] at hsplit_tri7
    have htet0_eq : β₈ (tet16W143 0) = tetBit0 canon := congrFun htet_bb8 0
    rw [htet_val8, htet0_eq] at hsplit_tet8
    have htv_le : triNum canon.v.val ≤ 2080 := triNum_le_2080 canon.v
    have htw_lt : tetNum canon.w.val < 47905 := by
      have := (tetRank65 canon).isLt
      have hpoly : (tetRank65 canon).val = tetNum canon.w.val + triNum canon.v.val + canon.u.val :=
          rfl
      dsimp [orbitCount47905] at this; omega
    have h215 : (2 : ℕ) ^ (14 + 1) = 32768 := by decide
    have hz0_val : (0 : ZMod 2).val = 0 := rfl
    rw [hz0_val, add_zero, h215]
    set S_hi := bitsVal (fun i : Fin 11 ↦ β₇ (tri12W143 i.succ)) +
      bitsVal (fun i : Fin 15 ↦ β₈ (tet15HiW143 i))
    have htetHi_def : (fun i : Fin 15 ↦ β₈ (tet15HiW143 i)) = fun i ↦ β₈ (tet16W143 i.succ) := rfl
    have hlt_hi : S_hi < 32768 := by
      dsimp only [S_hi]; rw [htetHi_def]; omega
    rw [Nat.mod_eq_of_lt hlt_hi]
    dsimp only [S_hi]
    rw [htetHi_def]
    omega
  have hbits9 : (fun k : Fin 16 ↦ β₉ (outVW16_143 k)) = basisBits 16 (outVWVal canon) :=
    (bits_eq_basisBits_of_val _).trans (congrArg (basisBits 16) (Fin.ext hout_val))
  exact ⟨fun k ↦ congrFun hbits9 k, htet0_keep9⟩
end IrredTailOpt143
theorem vwTail12OptCtx143_fwd : (∀ q : Wire 143, ScopedBlock 143 115 (probeFwd
    vwTail12OptCtx143) (.z q) (vwTail12OptCtx143.plug (.z q))) ∧ (∀ (β : BitAssignment 143) (c
    : CanonicalTriple65), cleanRem 143 115 β → (∀ k : Fin 12, β (wPack143 k) = packCanonVW12 c
    k) → bitsVal (fun k : Fin 16 ↦ vwTail12OptCtx143.fwdBits β (outVW16_143 k)) +
    (vwTail12OptCtx143.fwdBits β (tet16W143 0)).val = triNum c.v.val + tetNum c.w.val) := by
  have hMain : ∀ q₀ : Wire 143, ∃ fullSetup : BitAssignment 143 → BitAssignment 143,
      ScopedBlock 143 115 fullSetup (.z q₀) (vwTail12OptCtx143.plug (.z q₀)) ∧ ∀
      (β : BitAssignment 143) (c : CanonicalTriple65), cleanRem 143 115 β →
      (∀ k : Fin 12, β (wPack143 k) = packCanonVW12 c k) → (∀ j : Fin 16, fullSetup β
      (outVW16_143 j) = basisBits 16 (outVWVal c) j) ∧ fullSetup β (tet16W143 0) = tetBit0 c
      := by
    intro q₀
    obtain ⟨sTail, hTail, hSpecTail⟩ := vwLutAddOpt143_block q₀
    obtain ⟨hUnp, hSpecUnp⟩ := ScopedBlock.ctxUnpack12_143_block (.z q₀) (vwLutAddOpt143.plug (.z
        q₀)) sTail hTail
    let fullSetup : BitAssignment 143 → BitAssignment 143 := fun β ↦ sTail (setupUnpack12 β)
    have hPlug : vwTail12OptCtx143.plug (.z q₀) = ctxUnpack12_143.plug
        (vwLutAddOpt143.plug (.z q₀)) := TempCtx.append_plug _ _ _
    have hBlock115 : ScopedBlock 143 115 fullSetup (.z q₀) (vwTail12OptCtx143.plug (.z q₀)) :=
      ⟨hPlug ▸ pkValidCleanRemUp (by decide) hUnp.valid,
        fun β hβ ↦ by rw [hPlug]; exact hUnp.bits β (fun u hu ↦ hβ u (by omega)),
        fun β hβ ↦ by rw [hPlug]; exact hUnp.sign β (fun u hu ↦ hβ u (by omega))⟩
    refine ⟨fullSetup, hBlock115, fun β c hβ hpack ↦ ?_⟩
    have hz0 : β wZero143 = 0 := hβ wZero143 (by decide)
    obtain ⟨hcl32, hz0_unp, hv_val, hw_val⟩ := hSpecUnp β c (fun u hu ↦ hβ u (by omega)) hpack
    exact hSpecTail (setupUnpack12 β) c hcl32 (hz0_unp.trans hz0) hv_val hw_val
  refine ⟨scopedBlock_probeFwd vwTail12OptCtx143
      (fun q ↦ let ⟨s, h, _⟩ := hMain q; ⟨s, h⟩),
    fun β c hβ hpack ↦ ?_⟩
  have hOut : (fun k : Fin 16 ↦ vwTail12OptCtx143.fwdBits β (outVW16_143 k)) =
      basisBits 16 (outVWVal c) := by
    funext j
    obtain ⟨s_j, h_j, hval_j⟩ := hMain (outVW16_143 j)
    exact (vwTail12OptCtx143.plug_evalSign (.z (outVW16_143 j)) β).symm.trans
      ((h_j.sign β hβ).trans ((hval_j β c hβ hpack).1 j))
  have hCin : vwTail12OptCtx143.fwdBits β (tet16W143 0) = tetBit0 c := by
    obtain ⟨s_0, h_0, hval_0⟩ := hMain (tet16W143 0)
    exact (vwTail12OptCtx143.plug_evalSign (.z (tet16W143 0)) β).symm.trans
      ((h_0.sign β hβ).trans (hval_0 β c hβ hpack).2)
  rw [hOut, bitsVal_basisBits, hCin]
  dsimp only [outVWVal]
  have hle := (tetBit0_le_vw c).1
  omega
attribute [irreducible] vwTail12OptCtx143
/-- Auxiliary definition `addTail12OptProg143`. -/
def addTail12OptProg143 : TempPhaseProg 143 := vwTail12OptCtx143.plug addOrbBody143
private theorem orbTailProg143_full_spec_gen {rem cntTot : ℕ} (ctx : TempCtx 143)
    (body : TempPhaseProg 143) (hDS : ctx.DisjointFrom mutOrb143 ∧ ctx.SupportsBelowCtx 128)
    (hrem : 143 - 128 ≤ rem) (hProbe : ∀ q : Wire 143, ScopedBlock 143 rem (probeFwd ctx) (.z
    q) (ctx.plug (.z q))) (hvB : ValidCleanRem 143 (143 - 128) body)
    (hsgnB : ∀ γ, body.evalSign γ = 0) (hnmB : ∀ γ w, ¬ mutOrb143 w → body.evalBits γ w = γ w)
    (hTot : ctx.countTempAnd + body.countTempAnd = cntTot) : ValidCleanRem 143 rem
    (ctx.plug body) ∧ (ctx.plug body).countTempAnd = cntTot ∧ (∀ β : BitAssignment 143,
    cleanRem 143 rem β → (ctx.plug body).evalSign β = 0) ∧ (∀ β : BitAssignment 143, cleanRem
    143 rem β → ∀ w : Wire 143, (ctx.plug body).evalBits β w = if mutOrb143 w then
    body.evalBits (ctx.fwdBits β) w else β w) := by
  obtain ⟨hVal, hCnt, hSgn, hBits⟩ := ScopedBlock.graft_mutating_body
    (M := 143) (rem := rem) (curHole := 128) mutOrb143 ctx hDS.1 hDS.2 hrem
    (probeFwd ctx) hProbe body hvB hnmB
  refine ⟨hVal, by rw [hCnt, hTot], fun β hcl ↦ by rw [hSgn β hcl, hsgnB], fun β hcl w ↦ ?_⟩
  rw [hBits β hcl w]
  by_cases hm : mutOrb143 w
  · rw [pkItePos hm, pkItePos hm,
      show probeFwd ctx β = ctx.fwdBits β from funext fun q ↦ ctx.plug_evalSign (.z q) β]
  · rw [pkIteNeg hm, pkIteNeg hm]
theorem addTail12OptProg143_full_spec : ValidCleanRem 143 115 addTail12OptProg143 ∧
    addTail12OptProg143.countTempAnd = 79 ∧ (∀ β : BitAssignment 143, cleanRem 143 115 β →
    addTail12OptProg143.evalSign β = 0) ∧ (∀ β : BitAssignment 143, cleanRem 143 115 β → ∀ w :
    Wire 143, addTail12OptProg143.evalBits β w = if mutOrb143 w then addOrbBody143.evalBits
    (vwTail12OptCtx143.fwdBits β) w else β w) := by
  obtain ⟨hvB, hcntB, hsgnB, hnmB, _⟩ := addOrbBody143_spec
  exact orbTailProg143_full_spec_gen vwTail12OptCtx143 addOrbBody143
    vwTail12OptCtx143_disj_supp (by decide) vwTail12OptCtx143_fwd.1 hvB hsgnB hnmB
    (by rw [vwTail12OptCtx143_countTempAnd, hcntB])
attribute [irreducible] addTail12OptProg143
/-- Auxiliary definition `subTail12OptProg143`. -/
def subTail12OptProg143 : TempPhaseProg 143 := vwTail12OptCtx143.plug subOrbBody143
theorem subTail12OptProg143_full_spec : ValidCleanRem 143 115 subTail12OptProg143 ∧
    subTail12OptProg143.countTempAnd = 79 ∧ (∀ β : BitAssignment 143, cleanRem 143 115 β →
    subTail12OptProg143.evalSign β = 0) ∧ (∀ β : BitAssignment 143, cleanRem 143 115 β → ∀ w :
    Wire 143, subTail12OptProg143.evalBits β w = if mutOrb143 w then subOrbBody143.evalBits
    (vwTail12OptCtx143.fwdBits β) w else β w) := by
  obtain ⟨hvB, hcntB, hsgnB, hnmB⟩ := subOrbBody143_spec
  exact orbTailProg143_full_spec_gen vwTail12OptCtx143 subOrbBody143
    vwTail12OptCtx143_disj_supp (by decide) vwTail12OptCtx143_fwd.1 hvB hsgnB hnmB
    (by rw [vwTail12OptCtx143_countTempAnd, hcntB])
attribute [irreducible] subTail12OptProg143
/-- `316 T`, `0` `TOFF` circuit adding `triNum v + tetNum w` mod `2^16` into `rOrbit16`
from `rHold12` using `115` clean wires `rClean.slice 12 115`. -/
def dAddTailFrom12Opt {Var : Type} {n mClean : ℕ} (hmClean : 138 ≤ mClean) (v : Var)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) : DynamicCircuit Var n :=
  (addTail12OptProg143.onRegister (rCombTail143 hmClean rOrbit16 rClean hOW)).toDyn v
/-- `316 T`, `0` `TOFF` circuit subtracting `triNum v + tetNum w` mod `2^16` from `rOrbit16`
using `rHold12` and `115` clean wires `rClean.slice 12 115`. -/
def dSubTailFrom12Opt {Var : Type} {n mClean : ℕ} (hmClean : 138 ≤ mClean) (v : Var)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) : DynamicCircuit Var n :=
  (subTail12OptProg143.onRegister (rCombTail143 hmClean rOrbit16 rClean hOW)).toDyn v
theorem count_dAddTailFrom12Opt_toff {Var : Type} {n mClean : ℕ} (hmClean : 138 ≤ mClean)
    (v : Var) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) :
    (dAddTailFrom12Opt hmClean v rOrbit16 rClean hOW).count TOFF = 0 :=
  TempPhaseProg.toDyn_count_toff v _
theorem count_dAddTailFrom12Opt_t {Var : Type} {n mClean : ℕ} (hmClean : 138 ≤ mClean)
    (v : Var) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) :
    (dAddTailFrom12Opt hmClean v rOrbit16 rClean hOW).count T = 316 := by
  dsimp only [dAddTailFrom12Opt]
  rw [TempPhaseProg.toDyn_count_t, TempPhaseProg.onRegister_countTempAnd,
    addTail12OptProg143_full_spec.2.1]
theorem count_dSubTailFrom12Opt_toff {Var : Type} {n mClean : ℕ} (hmClean : 138 ≤ mClean)
    (v : Var) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) :
    (dSubTailFrom12Opt hmClean v rOrbit16 rClean hOW).count TOFF = 0 :=
  TempPhaseProg.toDyn_count_toff v _
theorem count_dSubTailFrom12Opt_t {Var : Type} {n mClean : ℕ} (hmClean : 138 ≤ mClean)
    (v : Var) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) :
    (dSubTailFrom12Opt hmClean v rOrbit16 rClean hOW).count T = 316 := by
  dsimp only [dSubTailFrom12Opt]
  rw [TempPhaseProg.toDyn_count_t, TempPhaseProg.onRegister_countTempAnd,
    subTail12OptProg143_full_spec.2.1]
/-- Auxiliary definition `addTailStep12Opt`. -/
noncomputable def addTailStep12Opt {n mClean : ℕ} (hmClean : 138 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) (β : BitAssignment n) : BitAssignment n :=
  let rComb := rCombTail143 hmClean rOrbit16 rClean hOW
  writeReg β rOrbit16 (fun k ↦
    addOrbBody143.evalBits (vwTail12OptCtx143.fwdBits (fun u ↦ β (rComb u))) (wOrb143 k))
/-- Auxiliary definition `subTailStep12Opt`. -/
noncomputable def subTailStep12Opt {n mClean : ℕ} (hmClean : 138 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) (β : BitAssignment n) : BitAssignment n :=
  let rComb := rCombTail143 hmClean rOrbit16 rClean hOW
  writeReg β rOrbit16 (fun k ↦
    subOrbBody143.evalBits (vwTail12OptCtx143.fwdBits (fun u ↦ β (rComb u))) (wOrb143 k))
theorem addTailStep12Opt_apply_non_orb {n mClean : ℕ} (hmClean : 138 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) (β : BitAssignment n) {q : Fin n}
    (hq : q ∉ Set.range rOrbit16.wires) : addTailStep12Opt hmClean rOrbit16 rClean hOW β q = β
    q := writeReg_apply_of_not_mem _ rOrbit16 _ _ hq
theorem subTailStep12Opt_apply_non_orb {n mClean : ℕ} (hmClean : 138 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) (β : BitAssignment n) {q : Fin n}
    (hq : q ∉ Set.range rOrbit16.wires) : subTailStep12Opt hmClean rOrbit16 rClean hOW β q = β
    q := writeReg_apply_of_not_mem _ rOrbit16 _ _ hq
theorem addTailStep12Opt_preserves_mid12 {n mClean : ℕ} (hmClean : 138 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) {β : BitAssignment n}
    (hβ : S_mid12 hmClean rClean β) :
    S_mid12 hmClean rClean (addTailStep12Opt hmClean rOrbit16 rClean hOW β) := fun j ↦ by
  have hnotO : rCleanMid12 hmClean rClean j ∉ Set.range rOrbit16.wires := by
    rintro ⟨k, hk⟩
    exact hOW.ne k ⟨12 + j.val, by omega⟩ (hk.trans (QRegister.slice_apply rClean 12 _ _ j))
  rw [addTailStep12Opt_apply_non_orb hmClean rOrbit16 rClean hOW β hnotO]
  exact hβ j
theorem subTailStep12Opt_preserves_mid12 {n mClean : ℕ} (hmClean : 138 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) {β : BitAssignment n}
    (hβ : S_mid12 hmClean rClean β) :
    S_mid12 hmClean rClean (subTailStep12Opt hmClean rOrbit16 rClean hOW β) := fun j ↦ by
  have hnotO : rCleanMid12 hmClean rClean j ∉ Set.range rOrbit16.wires := by
    rintro ⟨k, hk⟩
    exact hOW.ne k ⟨12 + j.val, by omega⟩ (hk.trans (QRegister.slice_apply rClean 12 _ _ j))
  rw [subTailStep12Opt_apply_non_orb hmClean rOrbit16 rClean hOW β hnotO]
  exact hβ j
theorem cleanRem115_rCombTail143 {n mClean : ℕ} (hmClean : 138 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) {β : BitAssignment n}
    (hs : S_mid12 hmClean rClean β) :
    cleanRem 143 115 (fun u ↦ β (rCombTail143 hmClean rOrbit16 rClean hOW u)) := fun u hu ↦ by
  let j : Fin 115 := ⟨u.val - 28, by omega⟩
  have hu_eq : u = ⟨28 + j.val, by omega⟩ := by ext; dsimp [j]; omega
  change β (rCombTail143 hmClean rOrbit16 rClean hOW u) = 0
  rw [hu_eq, rCombTail143_scr hmClean rOrbit16 rClean hOW j]
  exact hs ⟨j.val, by omega⟩
theorem cleanRem15_fwdBits_vwTail12OptCtx143 {α : BitAssignment 143}
    (hcl : cleanRem 143 115 α) :
    cleanRem 143 (143 - 128) (vwTail12OptCtx143.fwdBits α) := fun u hu ↦ by
  rw [TempCtx.fwdBits_outside vwTail12OptCtx143 vwTail12OptCtx143_disj_supp.2 α u (by omega)]
  exact hcl u (by omega)
private noncomputable abbrev orbBodyStep143 {n : ℕ} (body : TempPhaseProg 143)
    (ctx : TempCtx 143) (rOrbit16 : QRegister 16 n) (rComb : QRegister 143 n)
    (β : BitAssignment n) : BitAssignment n := writeReg β rOrbit16 (fun k ↦ body.evalBits
    (ctx.fwdBits (fun u ↦ β (rComb u))) (wOrb143 k))
private theorem subTailStepOpt_cancel_gen {n : ℕ} (ctx : TempCtx 143)
    (hDisj : ctx.DisjointFrom mutOrb143) (rOrbit16 : QRegister 16 n) (rComb : QRegister 143 n)
    (hCombOrb : ∀ j : Fin 16, rComb (wOrb143 j) = rOrbit16 j) (β : BitAssignment n) (hcl₁ :
    cleanRem 143 (143 - 128) (ctx.fwdBits (fun u ↦ β (rComb u)))) (hcl₂ : cleanRem 143 (143 -
    128) (ctx.fwdBits (fun u ↦ orbBodyStep143 addOrbBody143 ctx rOrbit16 rComb β (rComb u))))
    : orbBodyStep143 subOrbBody143 ctx rOrbit16 rComb
    (orbBodyStep143 addOrbBody143 ctx rOrbit16 rComb β) = β := by
  let β₁ := orbBodyStep143 addOrbBody143 ctx rOrbit16 rComb β
  let γ₁ := ctx.fwdBits (fun u ↦ β (rComb u))
  let γ₂ := ctx.fwdBits (fun u ↦ β₁ (rComb u))
  have hNonMutEq : ∀ w : Wire 143, ¬ mutOrb143 w → γ₂ w = γ₁ w := fun w hnm ↦ by
    refine OrbitSandHeld46.fwdBits_congr_nonMut hDisj (fun u hu ↦ ?_) w hnm
    have hnotO : rComb u ∉ Set.range rOrbit16.wires := fun ⟨j, hj⟩ ↦
      hu ⟨j, (rComb.wires.injective ((hCombOrb j).trans hj)).symm⟩
    exact writeReg_apply_of_not_mem _ rOrbit16 _ _ hnotO
  have hOut : ∀ j : Fin 16, γ₂ (outVW16_143 j) = γ₁ (outVW16_143 j) :=
    fun j ↦ hNonMutEq _ (not_mutOrb143_of_ge28 (outVW16_143_ge28 j))
  have hCin : γ₂ (tet16W143 0) = γ₁ (tet16W143 0) :=
    hNonMutEq _ (not_mutOrb143_of_ge28 (by decide))
  have hOrb : ∀ j : Fin 16, γ₂ (wOrb143 j) = addOrbBody143.evalBits γ₁ (wOrb143 j) := fun j ↦ by
    dsimp only [γ₂, β₁, orbBodyStep143]
    rw [TempCtx.fwdBits_mut hDisj _ ⟨j, rfl⟩, hCombOrb j, writeReg_apply_reg]
  have hCancel := subOrbBody143_addOrbBody143_cancel γ₁ γ₂ hcl₁ hcl₂ hOrb hOut hCin
  funext q
  by_cases hq : q ∈ Set.range rOrbit16.wires
  · obtain ⟨j, rfl⟩ := hq
    change writeReg β₁ rOrbit16 _ (rOrbit16 j) = _
    rw [writeReg_apply_reg, hCancel j]
    dsimp only [γ₁]
    rw [TempCtx.fwdBits_mut hDisj _ ⟨j, rfl⟩, hCombOrb j]
  · exact (writeReg_apply_of_not_mem _ rOrbit16 _ _ hq).trans
      (writeReg_apply_of_not_mem _ rOrbit16 _ _ hq)
set_option backward.isDefEq.respectTransparency true in
private theorem addOrbBody143_evalBits_eq_tetRank65 {γ : BitAssignment 143}
    (c : CanonicalTriple65) (hcl15 : cleanRem 143 (143 - 128) γ) (hvw : bitsVal (fun k : Fin
    16 ↦ γ (outVW16_143 k)) + (γ (tet16W143 0)).val = triNum c.v.val + tetNum c.w.val)
    (horb_val : bitsVal (fun k : Fin 16 ↦ γ (wOrb143 k)) = c.u.val) (j : Fin 16) :
    addOrbBody143.evalBits γ (wOrb143 j) = basisBits 16
    ⟨(tetRank65 c).val, lt_trans (tetRank65 c).isLt (by decide)⟩ j := by
  obtain ⟨_, _, _, _, hvalA⟩ := addOrbBody143_spec
  have hsum_val : bitsVal (fun k : Fin 16 ↦ addOrbBody143.evalBits γ (wOrb143 k)) =
      (tetRank65 c).val := by
    rw [hvalA γ hcl15, horb_val]
    have hpoly : (tetRank65 c).val = tetNum c.w.val + triNum c.v.val + c.u.val := rfl
    have hlt : (tetRank65 c).val < 65536 := by
      have := (tetRank65 c).isLt
      dsimp [orbitCount47905] at this
      omega
    have hadd : bitsVal (fun k : Fin 16 ↦ γ (outVW16_143 k)) + c.u.val + (γ (tet16W143 0)).val =
        (tetRank65 c).val := by omega
    rw [hadd, Nat.mod_eq_of_lt hlt]
  exact congrFun ((bits_eq_basisBits_of_val (fun k : Fin 16 ↦ addOrbBody143.evalBits γ (wOrb143
      k))).trans
    (congrArg (basisBits 16) (Fin.ext hsum_val))) j
theorem subTailStep12Opt_addTailStep12Opt_cancel {n mClean : ℕ} (hmClean : 138 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) {β : BitAssignment n}
    (hs : S_mid12 hmClean rClean β) : subTailStep12Opt hmClean rOrbit16 rClean hOW
    (addTailStep12Opt hmClean rOrbit16 rClean hOW β) = β := by
  exact subTailStepOpt_cancel_gen vwTail12OptCtx143 vwTail12OptCtx143_disj_supp.1 rOrbit16
    (rCombTail143 hmClean rOrbit16 rClean hOW) (rCombTail143_orb hmClean rOrbit16 rClean hOW)
    β (cleanRem15_fwdBits_vwTail12OptCtx143 (cleanRem115_rCombTail143 hmClean rOrbit16 rClean
    hOW hs)) (cleanRem15_fwdBits_vwTail12OptCtx143 (cleanRem115_rCombTail143 hmClean rOrbit16
    rClean hOW (addTailStep12Opt_preserves_mid12 hmClean rOrbit16 rClean hOW hs)))
theorem addTailStep12Opt_apply_orb_of_packed {n mClean : ℕ} (hmClean : 138 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) {β : BitAssignment n}
    (hs : S_mid12 hmClean rClean β) (c : CanonicalTriple65)
    (hpack : ∀ k : Fin 12, β (rHold12 hmClean rClean k) = packCanonVW12 c k)
    (hu_orb : ∀ j : Fin 16, β (rOrbit16 j) = packCanon28 c (Fin.natAdd 12 j)) (j : Fin 16) :
    addTailStep12Opt hmClean rOrbit16 rClean hOW β (rOrbit16 j) =
      basisBits 16 ⟨(tetRank65 c).val, lt_trans (tetRank65 c).isLt (by decide)⟩ j := by
  let rComb := rCombTail143 hmClean rOrbit16 rClean hOW
  let α : BitAssignment 143 := fun u ↦ β (rComb u)
  let γ := vwTail12OptCtx143.fwdBits α
  have hcl115 := cleanRem115_rCombTail143 hmClean rOrbit16 rClean hOW hs
  have hcl15 := cleanRem15_fwdBits_vwTail12OptCtx143 hcl115
  have hpk143 : ∀ k : Fin 12, α (wPack143 k) = packCanonVW12 c k := fun k ↦ by
    dsimp only [α]; rw [rCombTail143_pack hmClean rOrbit16 rClean hOW k]; exact hpack k
  have hvw : bitsVal (fun k : Fin 16 ↦ γ (outVW16_143 k)) + (γ (tet16W143 0)).val = triNum
      c.v.val + tetNum c.w.val := vwTail12OptCtx143_fwd.2 α c hcl115 hpk143
  have horb_fn : (fun k : Fin 16 ↦ γ (wOrb143 k)) = fun k ↦ packCanon28 c (Fin.natAdd 12 k) := by
    funext k
    dsimp only [γ, α]
    rw [TempCtx.fwdBits_mut vwTail12OptCtx143_disj_supp.1 _ ⟨k, rfl⟩,
      rCombTail143_orb hmClean rOrbit16 rClean hOW k, hu_orb k]
  have horb_val : bitsVal (fun k : Fin 16 ↦ γ (wOrb143 k)) = c.u.val := by
    rw [horb_fn]; exact bitsVal_packCanon28_orb c
  dsimp only [addTailStep12Opt]
  rw [writeReg_apply_reg]
  exact addOrbBody143_evalBits_eq_tetRank65 c hcl15 hvw horb_val j
private theorem dTailFromOpt_constClean_gen {Var : Type} [Fintype Var] [DecidableEq Var]
    {n cnt : ℕ} (rem : ℕ) (hrem : rem ≤ 143) (v : Var) (rOrbit16 : QRegister 16 n)
    (rComb : QRegister 143 n) (prog body : TempPhaseProg 143) (ctx : TempCtx 143)
    (S_mid : BitAssignment n → Prop) (hFull : ValidCleanRem 143 rem prog ∧ prog.countTempAnd =
    cnt ∧ (∀ α, cleanRem 143 rem α → prog.evalSign α = 0) ∧ (∀ α, cleanRem 143 rem α → ∀ w,
    prog.evalBits α w = if mutOrb143 w then body.evalBits (ctx.fwdBits α) w else α w))
    (hCombOrb : ∀ k : Fin 16, rComb (wOrb143 k) = rOrbit16 k)
    (hclOfMid : ∀ {β}, S_mid β → cleanRem 143 rem (fun u ↦ β (rComb u))) : ∃ U : Unitary
    (2 ^ n), p2t_RealizesConstCleanUnitary (p2t_ketPredProj S_mid)
    ((prog.onRegister rComb).toDyn v) U ∧ ∀ β : BitAssignment n, S_mid β → U.1.mulVec (ket β)
    = ket (orbBodyStep143 body ctx rOrbit16 rComb β) := by
  obtain ⟨hVal, _, hSgn, hBits⟩ := hFull
  let U : Unitary (2 ^ n) := (prog.onRegister rComb).toToffCircuit.eval
  have hdRem : p2t_RealizesConstCleanUnitary
      (projZeroAll rem (tailScr rComb rem hrem)) ((prog.onRegister rComb).toDyn v) U :=
    PosSlots24SpectatorPrunedPhase.p2t_RealizesConstCleanUnitary_of_clean v
      (projZeroAll_conjTranspose rem _) (PreservesStoreConst_toDyn v _)
      (realizes_of_validCleanRem v rComb prog rem hrem hVal)
  have hSubProj : projZeroAll rem (tailScr rComb rem hrem) *
      p2t_ketPredProj S_mid = p2t_ketPredProj S_mid :=
    pk_projZeroAll_mul_ketPredProj _ fun β hs j ↦ by
      dsimp only [tailScr]
      refine hclOfMid hs _ ?_
      dsimp only
      omega
  refine ⟨U, p2t_RealizesConstCleanUnitary_mono_proj (projZeroAll_conjTranspose rem _)
    (p2t_ketPredProj_conjTranspose _) hSubProj hdRem, fun β hs ↦ ?_⟩
  have hcl := hclOfMid hs
  change ((prog.onRegister rComb).toToffCircuit.eval).1.mulVec (ket β) = _
  rw [eval_onRegister_prog_ket, hSgn _ hcl, ZMod.val_zero, _root_.pow_zero, one_smul]
  apply congrArg ket
  funext q
  by_cases hm : q ∈ Set.range rComb.wires
  · obtain ⟨u, rfl⟩ := hm
    rw [writeRegProg_apply_reg, hBits _ hcl u]
    by_cases hu : mutOrb143 u
    · obtain ⟨k, rfl⟩ := hu
      rw [pkItePos ⟨k, rfl⟩, hCombOrb k]
      dsimp only [orbBodyStep143]
      rw [writeReg_apply_reg]
    · rw [pkIteNeg hu]
      have hnotO : rComb u ∉ Set.range rOrbit16.wires := fun ⟨k, hk⟩ ↦
        hu ⟨k, (rComb.wires.injective ((hCombOrb k).trans hk)).symm⟩
      exact (writeReg_apply_of_not_mem _ rOrbit16 _ _ hnotO).symm
  · rw [writeRegProg_apply_of_not_mem _ _ _ _ hm]
    have hnotO : q ∉ Set.range rOrbit16.wires := fun ⟨k, hk⟩ ↦
      hm ⟨wOrb143 k, (hCombOrb k).trans hk⟩
    exact (writeReg_apply_of_not_mem _ rOrbit16 _ _ hnotO).symm
theorem dAddTailFrom12Opt_constClean {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mClean : ℕ} (hmClean : 138 ≤ mClean) (v : Var) (rOrbit16 : QRegister 16 n)
    (rClean : QRegister mClean n) (hOW : rOrbit16.DisjointWires rClean) : ∃ U_add : Unitary
    (2 ^ n), p2t_RealizesConstCleanUnitary (p2t_ketPredProj (S_mid12 hmClean rClean))
    (dAddTailFrom12Opt hmClean v rOrbit16 rClean hOW) U_add ∧ ∀ β : BitAssignment n,
    S_mid12 hmClean rClean β → U_add.1.mulVec (ket β) = ket
    (addTailStep12Opt hmClean rOrbit16 rClean hOW β) := by
  exact dTailFromOpt_constClean_gen 115 (by decide) v rOrbit16
    (rCombTail143 hmClean rOrbit16 rClean hOW) addTail12OptProg143 addOrbBody143
    vwTail12OptCtx143 (S_mid12 hmClean rClean) addTail12OptProg143_full_spec
    (rCombTail143_orb hmClean rOrbit16 rClean hOW)
    (cleanRem115_rCombTail143 hmClean rOrbit16 rClean hOW)
theorem dSubTailFrom12Opt_constClean {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mClean : ℕ} (hmClean : 138 ≤ mClean) (v : Var) (rOrbit16 : QRegister 16 n)
    (rClean : QRegister mClean n) (hOW : rOrbit16.DisjointWires rClean) : ∃ U_sub : Unitary
    (2 ^ n), p2t_RealizesConstCleanUnitary (p2t_ketPredProj (S_mid12 hmClean rClean))
    (dSubTailFrom12Opt hmClean v rOrbit16 rClean hOW) U_sub ∧ ∀ β : BitAssignment n,
    S_mid12 hmClean rClean β → U_sub.1.mulVec (ket β) = ket
    (subTailStep12Opt hmClean rOrbit16 rClean hOW β) := by
  exact dTailFromOpt_constClean_gen 115 (by decide) v rOrbit16
    (rCombTail143 hmClean rOrbit16 rClean hOW) subTail12OptProg143 subOrbBody143
    vwTail12OptCtx143 (S_mid12 hmClean rClean) subTail12OptProg143_full_spec
    (rCombTail143_orb hmClean rOrbit16 rClean hOW)
    (cleanRem115_rCombTail143 hmClean rOrbit16 rClean hOW)
attribute [irreducible] dAddTailFrom12Opt dSubTailFrom12Opt
/-- `1,400 + dMid.count T` `.T` packed-`12` orbit-rank phase sandwich (`hmClean : 138 ≤ mClean`),
holding `rClean.slice 0 12` (`12` wires) across `dMid` and passing `rClean.slice 12 (mClean - 12)`
(`126+` wires) to `dMid`. -/
def dOrbitSandPacked12Opt {Var : Type} {n : ℕ} (mClean : ℕ) (hmClean : 138 ≤ mClean)
    (slot2SwappedTo0 : Bool) (v : Var) (rCore : QRegister posCoreWires n)
    (rPartner18 : QRegister 18 n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean)
    (dMid : DynamicCircuit Var n) : DynamicCircuit Var n :=
  let dPk := dPack12 hmClean slot2SwappedTo0 v rCore rPartner18 rOrbit16 rClean
    hCP hCO hCW hPO hPW hOW
  let dAdd := dAddTailFrom12Opt hmClean v rOrbit16 rClean hOW
  let dSub := dSubTailFrom12Opt hmClean v rOrbit16 rClean hOW
  .seq dPk (.seq dAdd (.seq dMid (.seq dSub dPk)))
theorem count_dOrbitSandPacked12Opt_toff {Var : Type} {n : ℕ} (mClean : ℕ)
    (hmClean : 138 ≤ mClean) (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean)
    (dMid : DynamicCircuit Var n) : (dOrbitSandPacked12Opt mClean hmClean slot2SwappedTo0
    v rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW dMid).count TOFF = dMid.count
    TOFF := by
  dsimp only [dOrbitSandPacked12Opt, DynamicCircuit.count]
  rw [count_dPack12_toff, count_dAddTailFrom12Opt_toff, count_dSubTailFrom12Opt_toff]
  omega
theorem count_dOrbitSandPacked12Opt_t {Var : Type} {n : ℕ} (mClean : ℕ)
    (hmClean : 138 ≤ mClean) (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean)
    (dMid : DynamicCircuit Var n) : (dOrbitSandPacked12Opt mClean hmClean slot2SwappedTo0
    v rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW dMid).count T = 1400 +
    dMid.count T := by
  dsimp only [dOrbitSandPacked12Opt, DynamicCircuit.count]
  rw [count_dPack12_t, count_dAddTailFrom12Opt_t, count_dSubTailFrom12Opt_t]
  omega
private theorem dOrbitSandPackedOpt_realizes_gen {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mClean kHold : ℕ} (hk : kHold ≤ mClean) (slot2SwappedTo0 : Bool)
    (midPhase : Fin (2 ^ (posCoreWires + 16)) → Bool)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hOW : rOrbit16.DisjointWires rClean)
    (dPk dAdd dMid dSub : DynamicCircuit Var n)
    (pkStep addStep subStep : BitAssignment n → BitAssignment n)
    (hMid : DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rCore.concat rOrbit16 hCO) (rClean.slice kHold (mClean - kHold) (by omega))
      (diagSignUnitary midPhase) dMid)
    (hPk : ∃ U_pk : Unitary (2 ^ n),
      p2t_RealizesConstCleanUnitary
        (p2t_ketPredProj fun β ↦ ∀ j, β (rClean.slice kHold (mClean - kHold) (by omega) j) = 0)
        dPk U_pk ∧
      ∀ β, (∀ j, β (rClean.slice kHold (mClean - kHold) (by omega) j) = 0) →
        U_pk.1.mulVec (ket β) = ket (pkStep β))
    (hAdd : ∃ U_add : Unitary (2 ^ n),
      p2t_RealizesConstCleanUnitary
        (p2t_ketPredProj fun β ↦ ∀ j, β (rClean.slice kHold (mClean - kHold) (by omega) j) = 0)
        dAdd U_add ∧
      ∀ β, (∀ j, β (rClean.slice kHold (mClean - kHold) (by omega) j) = 0) →
        U_add.1.mulVec (ket β) = ket (addStep β))
    (hSub : ∃ U_sub : Unitary (2 ^ n),
      p2t_RealizesConstCleanUnitary
        (p2t_ketPredProj fun β ↦ ∀ j, β (rClean.slice kHold (mClean - kHold) (by omega) j) = 0)
        dSub U_sub ∧
      ∀ β, (∀ j, β (rClean.slice kHold (mClean - kHold) (by omega) j) = 0) →
        U_sub.1.mulVec (ket β) = ket (subStep β))
    (hPresPk : ∀ {β}, (∀ j, β (rClean.slice kHold (mClean - kHold) (by omega) j) = 0) →
      ∀ j, pkStep β (rClean.slice kHold (mClean - kHold) (by omega) j) = 0)
    (hPresAdd : ∀ {β}, (∀ j, β (rClean.slice kHold (mClean - kHold) (by omega) j) = 0) →
      ∀ j, addStep β (rClean.slice kHold (mClean - kHold) (by omega) j) = 0)
    (hPresSub : ∀ {β}, (∀ j, β (rClean.slice kHold (mClean - kHold) (by omega) j) = 0) →
      ∀ j, subStep β (rClean.slice kHold (mClean - kHold) (by omega) j) = 0)
    (hCancel : ∀ {β}, (∀ j, β (rClean.slice kHold (mClean - kHold) (by omega) j) = 0) →
      subStep (addStep β) = β)
    (hInvol : ∀ β, pkStep (pkStep β) = β)
    (hKetEq : ∀ β, (∀ j : Fin 16, β (rOrbit16 j) = 0) →
      (∀ k : Fin kHold, β (rClean.slice 0 kHold (by omega) k) = 0) →
      (∀ j, pkStep β (rClean.slice kHold (mClean - kHold) (by omega) j) = 0) →
      (∀ i, addStep (pkStep β) (rCore i) = β (rCore i)) ∧
      (∀ j : Fin 16, addStep (pkStep β) (rOrbit16 j) =
        basisBits 16 ⟨(tetRank65 (canonTriple128 (rawOrbitCoord128 slot2SwappedTo0
          (fun i ↦ β (rCore i)) (fun i ↦ β (rPartner18 i))))).val,
          lt_trans (tetRank65 _).isLt (by decide)⟩ j)) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
      (rCore.concat rPartner18 hCP) (rOrbit16.concat rClean hOW)
      (diagSignUnitary (sandPhase18 slot2SwappedTo0 midPhase))
      (.seq dPk (.seq dAdd (.seq dMid (.seq dSub dPk)))) := by
  let rMid := rClean.slice kHold (mClean - kHold) (by omega)
  let S_mid : BitAssignment n → Prop := fun β ↦ ∀ j, β (rMid j) = 0
  let P_mid := p2t_ketPredProj S_mid
  have hPm_herm : P_midᴴ = P_mid := p2t_ketPredProj_conjTranspose _
  obtain ⟨U_pk, hdPk, hKetPk⟩ := hPk
  obtain ⟨U_add, hdAdd, hKetAdd⟩ := hAdd
  obtain ⟨U_sub, hdSub, hKetSub⟩ := hSub
  let rCO := rCore.concat rOrbit16 hCO
  let U_mid : Unitary (2 ^ n) := rCO.embedUnitary (diagSignUnitary midPhase)
  have hdMid : p2t_RealizesConstCleanUnitary P_mid dMid U_mid :=
    p2t_RealizesConstCleanUnitary_mono_proj (projZeroAll_conjTranspose (mClean - kHold) _) hPm_herm
      (pk_projZeroAll_mul_ketPredProj _ fun _ hs j ↦ hs j)
      (OrbitSandHeld46.constClean_of_embeddedCleanWorkspace rCO rMid (diagSignUnitary midPhase)
          dMid hMid)
  have hd45 := p2t_RealizesConstCleanUnitary_seq_proj hPm_herm hPm_herm hdSub hdPk
    (pk_ketPredProj_mul_unitary_ketPredProj U_sub.1 hKetSub fun _ hs ↦ hPresSub hs)
  have hd345 := p2t_RealizesConstCleanUnitary_seq_proj hPm_herm hPm_herm hdMid hd45
    (pk_ketPredProj_mul_smul_ketPredProj U_mid.1 fun α _ ↦
      OrbitSandHeld46.embedUnitary_diagSignUnitary_mulVec_ket_held46 rCO midPhase α)
  have hd2345 := p2t_RealizesConstCleanUnitary_seq_proj hPm_herm hPm_herm hdAdd hd345
    (pk_ketPredProj_mul_unitary_ketPredProj U_add.1 hKetAdd fun _ hs ↦ hPresAdd hs)
  have hdAllMid := p2t_RealizesConstCleanUnitary_seq_proj hPm_herm hPm_herm hdPk hd2345
    (pk_ketPredProj_mul_unitary_ketPredProj U_pk.1 hKetPk fun _ hs ↦ hPresPk hs)
  let rOW := rOrbit16.concat rClean hOW
  let S_ow : BitAssignment n → Prop := fun β ↦ ∀ i, β (rOW i) = 0
  have hPow_herm : (p2t_ketPredProj S_ow)ᴴ = p2t_ketPredProj S_ow := p2t_ketPredProj_conjTranspose _
  have hImpOW : ∀ β : BitAssignment n, S_ow β → S_mid β := fun β hs j ↦ by
    dsimp only [rMid]
    rw [QRegister.slice_apply,
      show rClean ⟨kHold + j.val, by omega⟩ = rOW (Fin.natAdd 16 ⟨kHold + j.val, by omega⟩) from
        (QRegister.concat_apply_right rOrbit16 rClean hOW _).symm]
    exact hs _
  have hdAllOW := p2t_RealizesConstCleanUnitary_mono_proj hPm_herm hPow_herm
    (p2t_ketPredProj_mul_imp hImpOW) hdAllMid
  let U_target : Unitary (2 ^ n) :=
    (rCore.concat rPartner18 hCP).embedUnitary (diagSignUnitary (sandPhase18 slot2SwappedTo0
        midPhase))
  have hCongr : ((((U_pk * U_sub) * U_mid) * U_add) * U_pk).1 * p2t_ketPredProj S_ow =
      U_target.1 * p2t_ketPredProj S_ow :=
    pk_ketPredProj_unitary_eq _ _ fun β hs_ow ↦ by
      have hs_mid := hImpOW β hs_ow
      have hs₁ := hPresPk hs_mid
      simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
      rw [hKetPk β hs_mid, hKetAdd (pkStep β) hs₁,
        OrbitSandHeld46.embedUnitary_diagSignUnitary_mulVec_ket_held46 rCO midPhase (addStep
            (pkStep β)),
        Matrix.mulVec_smul, hKetSub (addStep (pkStep β)) (hPresAdd hs₁), hCancel hs₁,
        Matrix.mulVec_smul, hKetPk (pkStep β) hs₁, hInvol β]
      have hzOrb : ∀ j : Fin 16, β (rOrbit16 j) = 0 := fun j ↦ by
        rw [(QRegister.concat_apply_left rOrbit16 rClean hOW j).symm]
        exact hs_ow _
      have hzHold : ∀ k : Fin kHold, β (rClean.slice 0 kHold (by omega) k) = 0 := fun k ↦ by
        rw [QRegister.slice_apply, (QRegister.concat_apply_right rOrbit16 rClean hOW _).symm]
        exact hs_ow _
      obtain ⟨hCoreEq, hOrbEq⟩ := hKetEq β hzOrb hzHold hs₁
      refine sandPhase18_ket_eq slot2SwappedTo0 midPhase rCore rPartner18 rOrbit16 hCP hCO
        β (addStep (pkStep β)) hCoreEq fun j ↦ ?_
      rw [hOrbEq j, ← congrFun (basisBits_orbitRankFin16_eq slot2SwappedTo0
        (fun i ↦ β (rCore i)) (fun i ↦ β (rPartner18 i))) j]
  have hdTarget : p2t_RealizesConstCleanUnitary (rOW.basisOutcomeProjector 0)
      (.seq dPk (.seq dAdd (.seq dMid (.seq dSub dPk)))) U_target := by
    rw [p2t_basisOutcomeProjector_zero_eq_ketPredProj rOW]
    exact p2t_RealizesConstCleanUnitary_congr_unitary hPow_herm hdAllOW hCongr
  exact p2t_RealizesConstCleanUnitary_toEmbeddedCleanWorkspace (rCore.concat rPartner18 hCP) rOW
    (diagSignUnitary (sandPhase18 slot2SwappedTo0 midPhase)) _ hdTarget
theorem dOrbitSandPacked12Opt_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} (mClean : ℕ) (hmClean : 138 ≤ mClean) (slot2SwappedTo0 : Bool)
    (midPhase : Fin (2 ^ (posCoreWires + 16)) → Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean)
    (dMid : DynamicCircuit Var n) (hMid :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (rCore.concat rOrbit16 hCO)
    (rClean.slice 12 (mClean - 12) (by omega)) (diagSignUnitary midPhase) dMid) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (rCore.concat rPartner18 hCP)
    (rOrbit16.concat rClean hOW) (diagSignUnitary (sandPhase18 slot2SwappedTo0 midPhase))
    (dOrbitSandPacked12Opt mClean hmClean slot2SwappedTo0 v rCore rPartner18 rOrbit16
    rClean hCP hCO hCW hPO hPW hOW dMid) := by
  let rT28 := rTarget28 hmClean rOrbit16 rClean hOW
  have hCT : rCore.DisjointWires rT28 :=
    (QRegExt.disjointWires_symm
      (pk_disj_concat_left _ (QRegExt.disjointWires_symm (hCW.compose_right _))
      (QRegExt.disjointWires_symm hCO)))
  have hPT : rPartner18.DisjointWires rT28 :=
    (QRegExt.disjointWires_symm
      (pk_disj_concat_left _ (QRegExt.disjointWires_symm (hPW.compose_right _))
      (QRegExt.disjointWires_symm hPO)))
  refine dOrbitSandPackedOpt_realizes_gen (kHold := 12) (by omega) slot2SwappedTo0 midPhase
    rCore rPartner18 rOrbit16 rClean hCP hCO hOW _ _ dMid _ _ _ _ hMid
    (dPack12_constClean hmClean slot2SwappedTo0 v rCore rPartner18 rOrbit16 rClean hCP hCO hCW
        hPO hPW hOW)
    (dAddTailFrom12Opt_constClean hmClean v rOrbit16 rClean hOW)
    (dSubTailFrom12Opt_constClean hmClean v rOrbit16 rClean hOW)
    (packStep28_preserves_mid12 hmClean slot2SwappedTo0 rCore rPartner18 rOrbit16 rClean hOW)
    (addTailStep12Opt_preserves_mid12 hmClean rOrbit16 rClean hOW)
    (subTailStep12Opt_preserves_mid12 hmClean rOrbit16 rClean hOW)
    (subTailStep12Opt_addTailStep12Opt_cancel hmClean rOrbit16 rClean hOW)
    (packStep28_invol slot2SwappedTo0 rCore rPartner18 rT28 hCT hPT) fun β hzOrb hzHold hs₁ ↦ ?_
  refine ⟨fun i ↦ (addTailStep12Opt_apply_non_orb hmClean rOrbit16 rClean hOW _
    (fun ⟨k, hk⟩ ↦ hCO.ne i k hk.symm)).trans
    (packStep28_apply_of_not_target _ _ _ _ _ fun k ↦ hCT.ne i k), fun j ↦ ?_⟩
  refine addTailStep12Opt_apply_orb_of_packed hmClean rOrbit16 rClean hOW hs₁ _ (fun k ↦ ?_) (fun k
      ↦ ?_) j
  · rw [← rTarget28_hold hmClean rOrbit16 rClean hOW k, packStep28_apply_target,
      rTarget28_hold hmClean rOrbit16 rClean hOW k]
    dsimp only [rHold12]
    rw [hzHold k, zero_add, packCanon28_hold]
  · rw [← rTarget28_orb hmClean rOrbit16 rClean hOW k, packStep28_apply_target,
      rTarget28_orb hmClean rOrbit16 rClean hOW k, hzOrb k, zero_add]
attribute [irreducible] dOrbitSandPacked12Opt
/-- `62`-`TempAnd` (`248 T`) Packed-13 tail context (`ctxUnpack13_143` + `vwLutAddOpt143`). -/
def vwTail13OptCtx143 : TempCtx 143 := ctxUnpack13_143.append vwLutAddOpt143
theorem vwTail13OptCtx143_countTempAnd : vwTail13OptCtx143.countTempAnd = 62 := rfl
theorem vwTail13OptCtx143_supp128B : ctxSupportsBelowB 128 vwTail13OptCtx143 = true := rfl
theorem vwTail13OptCtx143_disj_supp : vwTail13OptCtx143.DisjointFrom mutOrb143 ∧
    vwTail13OptCtx143.SupportsBelowCtx 128 := ⟨TempCtx.disjointFrom_append
    ctxUnpack13_143_disj_supp.1 vwLutAddOpt143_disj_supp.1,
    supportsBelowCtx_of_ctxSupportsBelowB vwTail13OptCtx143_supp128B⟩
theorem vwTail13OptCtx143_fwd :
    (∀ q : Wire 143, ScopedBlock 143 112 (probeFwd vwTail13OptCtx143)
      (.z q) (vwTail13OptCtx143.plug (.z q))) ∧
    (∀ (β : BitAssignment 143) (c : CanonicalTriple65),
      cleanRem 143 112 β →
      β wZero143 = 0 →
      (∀ k : Fin 12, β (wPack143 k) = packCanonVW13 c (Fin.castAdd 1 k)) →
      β wW6_143 = packCanonVW13 c ⟨12, by decide⟩ →
      bitsVal (fun k : Fin 16 ↦ vwTail13OptCtx143.fwdBits β (outVW16_143 k)) +
        (vwTail13OptCtx143.fwdBits β (tet16W143 0)).val =
        triNum c.v.val + tetNum c.w.val) := by
  have hMain : ∀ q₀ : Wire 143,
      ∃ fullSetup : BitAssignment 143 → BitAssignment 143,
        ScopedBlock 143 112 fullSetup (.z q₀) (vwTail13OptCtx143.plug (.z q₀)) ∧
        ∀ (β : BitAssignment 143) (c : CanonicalTriple65),
          cleanRem 143 112 β →
          β wZero143 = 0 →
          (∀ k : Fin 12, β (wPack143 k) = packCanonVW13 c (Fin.castAdd 1 k)) →
          β wW6_143 = packCanonVW13 c ⟨12, by decide⟩ →
          (∀ j : Fin 16, fullSetup β (outVW16_143 j) = basisBits 16 (outVWVal c) j) ∧
          fullSetup β (tet16W143 0) = tetBit0 c := by
    intro q₀
    obtain ⟨sTail, hTail, hSpecTail⟩ := vwLutAddOpt143_block q₀
    obtain ⟨hUnp, hSpecUnp⟩ := ScopedBlock.ctxUnpack13_143_block (.z q₀) (vwLutAddOpt143.plug (.z
        q₀)) sTail hTail
    let fullSetup : BitAssignment 143 → BitAssignment 143 := fun β ↦ sTail (setupUnpack13 β)
    have hPlug : vwTail13OptCtx143.plug (.z q₀) = ctxUnpack13_143.plug
        (vwLutAddOpt143.plug (.z q₀)) := TempCtx.append_plug _ _ _
    have hBlock112 : ScopedBlock 143 112 fullSetup (.z q₀) (vwTail13OptCtx143.plug (.z q₀)) :=
      ⟨hPlug ▸ hUnp.valid,
        fun β hβ ↦ by rw [hPlug]; exact hUnp.bits β hβ,
        fun β hβ ↦ by rw [hPlug]; exact hUnp.sign β hβ⟩
    refine ⟨fullSetup, hBlock112, fun β c hβ hz0 hpack12 hpackW6 ↦ ?_⟩
    obtain ⟨hcl32, hz0_unp, hv_val, hw_val⟩ := hSpecUnp β c hβ hpack12 hpackW6
    exact hSpecTail (setupUnpack13 β) c hcl32 (hz0_unp.trans hz0) hv_val hw_val
  refine ⟨scopedBlock_probeFwd vwTail13OptCtx143
      (fun q ↦ let ⟨s, h, _⟩ := hMain q; ⟨s, h⟩),
    fun β c hβ hz0 hpack12 hpackW6 ↦ ?_⟩
  have hOut : (fun k : Fin 16 ↦ vwTail13OptCtx143.fwdBits β (outVW16_143 k)) =
      basisBits 16 (outVWVal c) := by
    funext j
    obtain ⟨s_j, h_j, hval_j⟩ := hMain (outVW16_143 j)
    exact (vwTail13OptCtx143.plug_evalSign (.z (outVW16_143 j)) β).symm.trans
      ((h_j.sign β hβ).trans ((hval_j β c hβ hz0 hpack12 hpackW6).1 j))
  have hCin : vwTail13OptCtx143.fwdBits β (tet16W143 0) = tetBit0 c := by
    obtain ⟨s_0, h_0, hval_0⟩ := hMain (tet16W143 0)
    exact (vwTail13OptCtx143.plug_evalSign (.z (tet16W143 0)) β).symm.trans
      ((h_0.sign β hβ).trans (hval_0 β c hβ hz0 hpack12 hpackW6).2)
  rw [hOut, bitsVal_basisBits, hCin]
  dsimp only [outVWVal]
  have hle := (tetBit0_le_vw c).1
  omega
attribute [irreducible] vwTail13OptCtx143
/-- Auxiliary definition `addTail13OptProg143`. -/
def addTail13OptProg143 : TempPhaseProg 143 := vwTail13OptCtx143.plug addOrbBody143
/-- Auxiliary definition `subTail13OptProg143`. -/
def subTail13OptProg143 : TempPhaseProg 143 := vwTail13OptCtx143.plug subOrbBody143
theorem addTail13OptProg143_full_spec : ValidCleanRem 143 112 addTail13OptProg143 ∧
    addTail13OptProg143.countTempAnd = 77 ∧ (∀ β : BitAssignment 143, cleanRem 143 112 β →
    addTail13OptProg143.evalSign β = 0) ∧ (∀ β : BitAssignment 143, cleanRem 143 112 β → ∀ w :
    Wire 143, addTail13OptProg143.evalBits β w = if mutOrb143 w then addOrbBody143.evalBits
    (vwTail13OptCtx143.fwdBits β) w else β w) := by
  obtain ⟨hvB, hcntB, hsgnB, hnmB, _⟩ := addOrbBody143_spec
  exact orbTailProg143_full_spec_gen vwTail13OptCtx143 addOrbBody143
    vwTail13OptCtx143_disj_supp (by decide) vwTail13OptCtx143_fwd.1 hvB hsgnB hnmB
    (by rw [vwTail13OptCtx143_countTempAnd, hcntB])
theorem subTail13OptProg143_full_spec : ValidCleanRem 143 112 subTail13OptProg143 ∧
    subTail13OptProg143.countTempAnd = 77 ∧ (∀ β : BitAssignment 143, cleanRem 143 112 β →
    subTail13OptProg143.evalSign β = 0) ∧ (∀ β : BitAssignment 143, cleanRem 143 112 β → ∀ w :
    Wire 143, subTail13OptProg143.evalBits β w = if mutOrb143 w then subOrbBody143.evalBits
    (vwTail13OptCtx143.fwdBits β) w else β w) := by
  obtain ⟨hvB, hcntB, hsgnB, hnmB⟩ := subOrbBody143_spec
  exact orbTailProg143_full_spec_gen vwTail13OptCtx143 subOrbBody143
    vwTail13OptCtx143_disj_supp (by decide) vwTail13OptCtx143_fwd.1 hvB hsgnB hnmB
    (by rw [vwTail13OptCtx143_countTempAnd, hcntB])
attribute [irreducible] addTail13OptProg143 subTail13OptProg143
/-- `308 T`, `0` `TOFF` circuit adding `triNum v + tetNum w` mod `2^16` into `rOrbit16`
from `rHold13` using `rCleanMid13`. -/
def dAddTailFrom13Opt {Var : Type} {n mClean : ℕ} (hmClean : 139 ≤ mClean) (v : Var)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) : DynamicCircuit Var n :=
  (addTail13OptProg143.onRegister (rCombTail13_143 hmClean rOrbit16 rClean hOW)).toDyn v
/-- `308 T`, `0` `TOFF` circuit subtracting `triNum v + tetNum w` mod `2^16` from `rOrbit16`
using `rHold13` and `rCleanMid13`. -/
def dSubTailFrom13Opt {Var : Type} {n mClean : ℕ} (hmClean : 139 ≤ mClean) (v : Var)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) : DynamicCircuit Var n :=
  (subTail13OptProg143.onRegister (rCombTail13_143 hmClean rOrbit16 rClean hOW)).toDyn v
theorem count_dAddTailFrom13Opt_toff {Var : Type} {n mClean : ℕ} (hmClean : 139 ≤ mClean)
    (v : Var) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) :
    (dAddTailFrom13Opt hmClean v rOrbit16 rClean hOW).count TOFF = 0 :=
  TempPhaseProg.toDyn_count_toff v _
theorem count_dAddTailFrom13Opt_t {Var : Type} {n mClean : ℕ} (hmClean : 139 ≤ mClean)
    (v : Var) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) :
    (dAddTailFrom13Opt hmClean v rOrbit16 rClean hOW).count T = 308 := by
  dsimp only [dAddTailFrom13Opt]
  rw [TempPhaseProg.toDyn_count_t, TempPhaseProg.onRegister_countTempAnd,
    addTail13OptProg143_full_spec.2.1]
theorem count_dSubTailFrom13Opt_toff {Var : Type} {n mClean : ℕ} (hmClean : 139 ≤ mClean)
    (v : Var) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) :
    (dSubTailFrom13Opt hmClean v rOrbit16 rClean hOW).count TOFF = 0 :=
  TempPhaseProg.toDyn_count_toff v _
theorem count_dSubTailFrom13Opt_t {Var : Type} {n mClean : ℕ} (hmClean : 139 ≤ mClean)
    (v : Var) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) :
    (dSubTailFrom13Opt hmClean v rOrbit16 rClean hOW).count T = 308 := by
  dsimp only [dSubTailFrom13Opt]
  rw [TempPhaseProg.toDyn_count_t, TempPhaseProg.onRegister_countTempAnd,
    subTail13OptProg143_full_spec.2.1]
/-- Auxiliary definition `addTailStep13Opt`. -/
noncomputable def addTailStep13Opt {n mClean : ℕ} (hmClean : 139 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) (β : BitAssignment n) : BitAssignment n :=
  let rComb := rCombTail13_143 hmClean rOrbit16 rClean hOW
  writeReg β rOrbit16 (fun k ↦
    addOrbBody143.evalBits (vwTail13OptCtx143.fwdBits (fun u ↦ β (rComb u))) (wOrb143 k))
/-- Auxiliary definition `subTailStep13Opt`. -/
noncomputable def subTailStep13Opt {n mClean : ℕ} (hmClean : 139 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) (β : BitAssignment n) : BitAssignment n :=
  let rComb := rCombTail13_143 hmClean rOrbit16 rClean hOW
  writeReg β rOrbit16 (fun k ↦
    subOrbBody143.evalBits (vwTail13OptCtx143.fwdBits (fun u ↦ β (rComb u))) (wOrb143 k))
theorem addTailStep13Opt_apply_non_orb {n mClean : ℕ} (hmClean : 139 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) (β : BitAssignment n) {q : Fin n}
    (hq : q ∉ Set.range rOrbit16.wires) : addTailStep13Opt hmClean rOrbit16 rClean hOW β q = β
    q := writeReg_apply_of_not_mem _ rOrbit16 _ _ hq
theorem subTailStep13Opt_apply_non_orb {n mClean : ℕ} (hmClean : 139 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) (β : BitAssignment n) {q : Fin n}
    (hq : q ∉ Set.range rOrbit16.wires) : subTailStep13Opt hmClean rOrbit16 rClean hOW β q = β
    q := writeReg_apply_of_not_mem _ rOrbit16 _ _ hq
theorem addTailStep13Opt_preserves_mid13 {n mClean : ℕ} (hmClean : 139 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) {β : BitAssignment n}
    (hβ : S_mid13 hmClean rClean β) :
    S_mid13 hmClean rClean (addTailStep13Opt hmClean rOrbit16 rClean hOW β) := fun j ↦ by
  have hnotO : rCleanMid13 hmClean rClean j ∉ Set.range rOrbit16.wires := by
    rintro ⟨k, hk⟩
    exact hOW.ne k ⟨13 + j.val, by omega⟩ (hk.trans (QRegister.slice_apply rClean 13 _ _ j))
  rw [addTailStep13Opt_apply_non_orb hmClean rOrbit16 rClean hOW β hnotO]
  exact hβ j
theorem subTailStep13Opt_preserves_mid13 {n mClean : ℕ} (hmClean : 139 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) {β : BitAssignment n}
    (hβ : S_mid13 hmClean rClean β) :
    S_mid13 hmClean rClean (subTailStep13Opt hmClean rOrbit16 rClean hOW β) := fun j ↦ by
  have hnotO : rCleanMid13 hmClean rClean j ∉ Set.range rOrbit16.wires := by
    rintro ⟨k, hk⟩
    exact hOW.ne k ⟨13 + j.val, by omega⟩ (hk.trans (QRegister.slice_apply rClean 13 _ _ j))
  rw [subTailStep13Opt_apply_non_orb hmClean rOrbit16 rClean hOW β hnotO]
  exact hβ j
theorem cleanRem112_rCombTail13_143_opt {n mClean : ℕ} (hmClean : 139 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) {β : BitAssignment n}
    (hs : S_mid13 hmClean rClean β) :
    cleanRem 143 112 (fun u ↦ β (rCombTail13_143 hmClean rOrbit16 rClean hOW u)) := fun u hu ↦ by
  let j : Fin 112 := ⟨u.val - 31, by omega⟩
  have hu_eq : u = ⟨31 + j.val, by omega⟩ := by ext; dsimp [j]; omega
  change β (rCombTail13_143 hmClean rOrbit16 rClean hOW u) = 0
  rw [hu_eq, rCombTail13_143_scr112 hmClean rOrbit16 rClean hOW j]
  exact hs ⟨2 + j.val, by omega⟩
theorem cleanRem15_fwdBits_vwTail13OptCtx143 {α : BitAssignment 143}
    (hcl : cleanRem 143 112 α) :
    cleanRem 143 (143 - 128) (vwTail13OptCtx143.fwdBits α) := fun u hu ↦ by
  rw [TempCtx.fwdBits_outside vwTail13OptCtx143 vwTail13OptCtx143_disj_supp.2 α u (by omega)]
  exact hcl u (by omega)
theorem subTailStep13Opt_addTailStep13Opt_cancel {n mClean : ℕ} (hmClean : 139 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) {β : BitAssignment n}
    (hs : S_mid13 hmClean rClean β) : subTailStep13Opt hmClean rOrbit16 rClean hOW
    (addTailStep13Opt hmClean rOrbit16 rClean hOW β) = β := by
  exact subTailStepOpt_cancel_gen vwTail13OptCtx143 vwTail13OptCtx143_disj_supp.1
    rOrbit16 (rCombTail13_143 hmClean rOrbit16 rClean hOW)
    (rCombTail13_143_orb hmClean rOrbit16 rClean hOW) β
    (cleanRem15_fwdBits_vwTail13OptCtx143 (cleanRem112_rCombTail13_143_opt hmClean rOrbit16 rClean
        hOW hs))
    (cleanRem15_fwdBits_vwTail13OptCtx143 (cleanRem112_rCombTail13_143_opt hmClean rOrbit16 rClean
        hOW
      (addTailStep13Opt_preserves_mid13 hmClean rOrbit16 rClean hOW hs)))
theorem addTailStep13Opt_apply_orb_of_packed {n mClean : ℕ} (hmClean : 139 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) {β : BitAssignment n}
    (hs : S_mid13 hmClean rClean β) (c : CanonicalTriple65)
    (hpack : ∀ k : Fin 13, β (rHold13 hmClean rClean k) = packCanonVW13 c k)
    (hu_orb : ∀ j : Fin 16, β (rOrbit16 j) = packCanon29 c (Fin.natAdd 13 j)) (j : Fin 16) :
    addTailStep13Opt hmClean rOrbit16 rClean hOW β (rOrbit16 j) =
      basisBits 16 ⟨(tetRank65 c).val, lt_trans (tetRank65 c).isLt (by decide)⟩ j := by
  let rComb := rCombTail13_143 hmClean rOrbit16 rClean hOW
  let α : BitAssignment 143 := fun u ↦ β (rComb u)
  let γ := vwTail13OptCtx143.fwdBits α
  have hcl112 := cleanRem112_rCombTail13_143_opt hmClean rOrbit16 rClean hOW hs
  have hcl15 := cleanRem15_fwdBits_vwTail13OptCtx143 hcl112
  have hz0 : α wZero143 = 0 := by
    dsimp only [α]; rw [rCombTail13_143_zero hmClean rOrbit16 rClean hOW]; exact hs ⟨0, by omega⟩
  have hpk12 : ∀ k : Fin 12, α (wPack143 k) = packCanonVW13 c (Fin.castAdd 1 k) := fun k ↦ by
    dsimp only [α]; rw [rCombTail13_143_pack12 hmClean rOrbit16 rClean hOW k]; exact hpack
        (Fin.castAdd 1 k)
  have hpkW6 : α wW6_143 = packCanonVW13 c ⟨12, by decide⟩ := by
    dsimp only [α]; rw [rCombTail13_143_w6 hmClean rOrbit16 rClean hOW]; exact hpack ⟨12, by decide⟩
  have hvw : bitsVal (fun k : Fin 16 ↦ γ (outVW16_143 k)) + (γ (tet16W143 0)).val = triNum
      c.v.val + tetNum c.w.val := vwTail13OptCtx143_fwd.2 α c hcl112 hz0 hpk12 hpkW6
  have horb_fn : (fun k : Fin 16 ↦ γ (wOrb143 k)) = fun k ↦ packCanon29 c (Fin.natAdd 13 k) := by
    funext k
    dsimp only [γ, α]
    rw [TempCtx.fwdBits_mut vwTail13OptCtx143_disj_supp.1 _ ⟨k, rfl⟩,
      rCombTail13_143_orb hmClean rOrbit16 rClean hOW k, hu_orb k]
  have horb_val : bitsVal (fun k : Fin 16 ↦ γ (wOrb143 k)) = c.u.val := by
    rw [horb_fn]; exact bitsVal_packCanon29_orb c
  dsimp only [addTailStep13Opt]
  rw [writeReg_apply_reg]
  exact addOrbBody143_evalBits_eq_tetRank65 c hcl15 hvw horb_val j
theorem dAddTailFrom13Opt_constClean {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mClean : ℕ} (hmClean : 139 ≤ mClean) (v : Var) (rOrbit16 : QRegister 16 n)
    (rClean : QRegister mClean n) (hOW : rOrbit16.DisjointWires rClean) : ∃ U_add : Unitary
    (2 ^ n), p2t_RealizesConstCleanUnitary (p2t_ketPredProj (S_mid13 hmClean rClean))
    (dAddTailFrom13Opt hmClean v rOrbit16 rClean hOW) U_add ∧ ∀ β : BitAssignment n,
    S_mid13 hmClean rClean β → U_add.1.mulVec (ket β) = ket
    (addTailStep13Opt hmClean rOrbit16 rClean hOW β) := by
  exact dTailFromOpt_constClean_gen 112 (by decide) v rOrbit16
    (rCombTail13_143 hmClean rOrbit16 rClean hOW) addTail13OptProg143 addOrbBody143
    vwTail13OptCtx143 (S_mid13 hmClean rClean) addTail13OptProg143_full_spec
    (rCombTail13_143_orb hmClean rOrbit16 rClean hOW)
    (cleanRem112_rCombTail13_143_opt hmClean rOrbit16 rClean hOW)
theorem dSubTailFrom13Opt_constClean {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mClean : ℕ} (hmClean : 139 ≤ mClean) (v : Var) (rOrbit16 : QRegister 16 n)
    (rClean : QRegister mClean n) (hOW : rOrbit16.DisjointWires rClean) : ∃ U_sub : Unitary
    (2 ^ n), p2t_RealizesConstCleanUnitary (p2t_ketPredProj (S_mid13 hmClean rClean))
    (dSubTailFrom13Opt hmClean v rOrbit16 rClean hOW) U_sub ∧ ∀ β : BitAssignment n,
    S_mid13 hmClean rClean β → U_sub.1.mulVec (ket β) = ket
    (subTailStep13Opt hmClean rOrbit16 rClean hOW β) := by
  exact dTailFromOpt_constClean_gen 112 (by decide) v rOrbit16
    (rCombTail13_143 hmClean rOrbit16 rClean hOW) subTail13OptProg143 subOrbBody143
    vwTail13OptCtx143 (S_mid13 hmClean rClean) subTail13OptProg143_full_spec
    (rCombTail13_143_orb hmClean rOrbit16 rClean hOW)
    (cleanRem112_rCombTail13_143_opt hmClean rOrbit16 rClean hOW)
attribute [irreducible] dAddTailFrom13Opt dSubTailFrom13Opt
/-- `1,376 + dMid.count T` `.T` packed-`13` orbit-rank phase sandwich (`hmClean : 139 ≤ mClean`),
holding `rClean.slice 0 13` (`13` wires) across `dMid` and passing `rClean.slice 13 (mClean - 13)`
(`126+` wires) to `dMid`. -/
def dOrbitSandPacked13Opt {Var : Type} {n : ℕ} (mClean : ℕ) (hmClean : 139 ≤ mClean)
    (slot2SwappedTo0 : Bool) (v : Var) (rCore : QRegister posCoreWires n)
    (rPartner18 : QRegister 18 n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean)
    (dMid : DynamicCircuit Var n) : DynamicCircuit Var n :=
  let dPk := dPack13 hmClean slot2SwappedTo0 v rCore rPartner18 rOrbit16 rClean
    hCP hCO hCW hPO hPW hOW
  let dAdd := dAddTailFrom13Opt hmClean v rOrbit16 rClean hOW
  let dSub := dSubTailFrom13Opt hmClean v rOrbit16 rClean hOW
  .seq dPk (.seq dAdd (.seq dMid (.seq dSub dPk)))
@[simp] theorem count_dOrbitSandPacked13Opt_toff {Var : Type} {n : ℕ} (mClean : ℕ)
    (hmClean : 139 ≤ mClean) (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean)
    (dMid : DynamicCircuit Var n) : (dOrbitSandPacked13Opt mClean hmClean slot2SwappedTo0
    v rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW dMid).count TOFF = dMid.count
    TOFF := by
  dsimp only [dOrbitSandPacked13Opt, DynamicCircuit.count]
  rw [count_dPack13_toff, count_dAddTailFrom13Opt_toff, count_dSubTailFrom13Opt_toff]
  omega
theorem count_dOrbitSandPacked13Opt_t {Var : Type} {n : ℕ} (mClean : ℕ)
    (hmClean : 139 ≤ mClean) (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean)
    (dMid : DynamicCircuit Var n) : (dOrbitSandPacked13Opt mClean hmClean slot2SwappedTo0
    v rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW dMid).count T = 1376 +
    dMid.count T := by
  dsimp only [dOrbitSandPacked13Opt, DynamicCircuit.count]
  rw [count_dPack13_t, count_dAddTailFrom13Opt_t, count_dSubTailFrom13Opt_t]
  omega
theorem dOrbitSandPacked13Opt_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} (mClean : ℕ) (hmClean : 139 ≤ mClean) (slot2SwappedTo0 : Bool)
    (midPhase : Fin (2 ^ (posCoreWires + 16)) → Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean)
    (dMid : DynamicCircuit Var n) (hMid :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (rCore.concat rOrbit16 hCO)
    (rClean.slice 13 (mClean - 13) (by omega)) (diagSignUnitary midPhase) dMid) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (rCore.concat rPartner18 hCP)
    (rOrbit16.concat rClean hOW) (diagSignUnitary (sandPhase18 slot2SwappedTo0 midPhase))
    (dOrbitSandPacked13Opt mClean hmClean slot2SwappedTo0 v rCore rPartner18 rOrbit16
    rClean hCP hCO hCW hPO hPW hOW dMid) := by
  let rT29 := rTarget29 hmClean rOrbit16 rClean hOW
  have hCT : rCore.DisjointWires rT29 :=
    (QRegExt.disjointWires_symm
      (pk_disj_concat_left _ (QRegExt.disjointWires_symm (hCW.compose_right _))
      (QRegExt.disjointWires_symm hCO)))
  have hPT : rPartner18.DisjointWires rT29 :=
    (QRegExt.disjointWires_symm
      (pk_disj_concat_left _ (QRegExt.disjointWires_symm (hPW.compose_right _))
      (QRegExt.disjointWires_symm hPO)))
  refine dOrbitSandPackedOpt_realizes_gen (kHold := 13) (by omega) slot2SwappedTo0 midPhase
    rCore rPartner18 rOrbit16 rClean hCP hCO hOW _ _ dMid _ _ _ _ hMid
    (dPack13_constClean hmClean slot2SwappedTo0 v rCore rPartner18 rOrbit16 rClean hCP hCO hCW
        hPO hPW hOW)
    (dAddTailFrom13Opt_constClean hmClean v rOrbit16 rClean hOW)
    (dSubTailFrom13Opt_constClean hmClean v rOrbit16 rClean hOW)
    (packStep29_preserves_mid13 hmClean slot2SwappedTo0 rCore rPartner18 rOrbit16 rClean hOW)
    (addTailStep13Opt_preserves_mid13 hmClean rOrbit16 rClean hOW)
    (subTailStep13Opt_preserves_mid13 hmClean rOrbit16 rClean hOW)
    (subTailStep13Opt_addTailStep13Opt_cancel hmClean rOrbit16 rClean hOW)
    (packStep29_invol slot2SwappedTo0 rCore rPartner18 rT29 hCT hPT) fun β hzOrb hzHold hs₁ ↦ ?_
  refine ⟨fun i ↦ (addTailStep13Opt_apply_non_orb hmClean rOrbit16 rClean hOW _
    (fun ⟨k, hk⟩ ↦ hCO.ne i k hk.symm)).trans
    (packStep29_apply_of_not_target _ _ _ _ _ fun k ↦ hCT.ne i k), fun j ↦ ?_⟩
  refine addTailStep13Opt_apply_orb_of_packed hmClean rOrbit16 rClean hOW hs₁ _ (fun k ↦ ?_) (fun k
      ↦ ?_) j
  · rw [← rTarget29_hold hmClean rOrbit16 rClean hOW k, packStep29_apply_target,
      rTarget29_hold hmClean rOrbit16 rClean hOW k]
    dsimp only [rHold13]
    rw [hzHold k, zero_add, packCanon29_hold]
  · rw [← rTarget29_orb hmClean rOrbit16 rClean hOW k, packStep29_apply_target,
      rTarget29_orb hmClean rOrbit16 rClean hOW k, hzOrb k, zero_add]
attribute [irreducible] dOrbitSandPacked13Opt
/-- `14`-bit raw unpacked encoding of `(V, W)` (`0` `TempAnd`s to pack, `0` `TempAnd`s to
  unpack!). -/
def packVWBits14 (V W : Fin 7 → ZMod 2) (k : Fin 14) : ZMod 2 :=
  match k.val with
  | 0 => V 0
  | 1 => V 1
  | 2 => V 2
  | 3 => V 3
  | 4 => V 4
  | 5 => W 0
  | 6 => W 1
  | 7 => W 2
  | 8 => W 3
  | 9 => W 4
  | 10 => V 5
  | 11 => W 5
  | 12 => W 6
  | _ => V 6
/-- `14`-bit raw unpacked `(c.v, c.w)` vector for `c : CanonicalTriple65`. -/
def packCanonVW14 (c : CanonicalTriple65) : Fin 14 → ZMod 2 :=
  packVWBits14 (fin65Bits7 c.v) (fin65Bits7 c.w)
/-- First `14` clean wires holding raw `(V, W)` across `dMid`. -/
abbrev rHold14 {n mClean : ℕ} (hmClean : 140 ≤ mClean) (rClean : QRegister mClean n) :
    QRegister 14 n := rClean.slice 0 14 (by omega)
/-- Remaining `mClean - 14` clean wires passed to `dMid` / tail scratch. -/
abbrev rCleanMid14 {n mClean : ℕ} (hmClean : 140 ≤ mClean) (rClean : QRegister mClean n) :
    QRegister (mClean - 14) n := rClean.slice 14 (mClean - 14) (by omega)
theorem rHold14_disj_orbit16 {n mClean : ℕ} (hmClean : 140 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) : (rHold14 hmClean rClean).DisjointWires rOrbit16 :=
  QRegister.disjoint_iff.mpr fun i j heq ↦ by
    dsimp only [rHold14] at heq
    rw [QRegister.slice_apply] at heq
    exact hOW.ne j _ heq.symm
/-- Auxiliary definition `rTarget30`. -/
def rTarget30 {n mClean : ℕ} (hmClean : 140 ≤ mClean) (rOrbit16 : QRegister 16 n)
    (rClean : QRegister mClean n) (hOW : rOrbit16.DisjointWires rClean) : QRegister 30 n :=
  (rHold14 hmClean rClean).concat rOrbit16 (rHold14_disj_orbit16 hmClean rOrbit16 rClean hOW)
theorem rTarget30_hold {n mClean : ℕ} (hmClean : 140 ≤ mClean) (rOrbit16 : QRegister 16 n)
    (rClean : QRegister mClean n) (hOW : rOrbit16.DisjointWires rClean) (k : Fin 14) :
    rTarget30 hmClean rOrbit16 rClean hOW (Fin.castAdd 16 k) = rHold14 hmClean rClean k :=
    QRegister.concat_apply_left (rHold14 hmClean rClean) rOrbit16
    (rHold14_disj_orbit16 hmClean rOrbit16 rClean hOW) k
theorem rTarget30_orb {n mClean : ℕ} (hmClean : 140 ≤ mClean) (rOrbit16 : QRegister 16 n)
    (rClean : QRegister mClean n) (hOW : rOrbit16.DisjointWires rClean) (j : Fin 16) :
    rTarget30 hmClean rOrbit16 rClean hOW (Fin.natAdd 14 j) = rOrbit16 j :=
    QRegister.concat_apply_right (rHold14 hmClean rClean) rOrbit16
    (rHold14_disj_orbit16 hmClean rOrbit16 rClean hOW) j
theorem rCombPack162_disj_target30 {n mClean : ℕ} (hmClean : 140 ≤ mClean)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean) :
    (rCombPack162 (by omega : 138 ≤ mClean) rCore rPartner18 rClean hCP hCW hPW).DisjointWires
    (rTarget30 hmClean rOrbit16 rClean hOW) := by
  have hActClean : (rCore.concat rPartner18 hCP).DisjointWires rClean :=
    pk_disj_concat_left hCP hCW hPW
  have h43Clean : ((rCore.concat rPartner18 hCP).compose sel43Reg).DisjointWires rClean :=
    QRegister.disjoint_iff.mpr fun i j heq ↦ hActClean.ne (sel43Reg i) j heq
  have hActOrb : (rCore.concat rPartner18 hCP).DisjointWires rOrbit16 :=
    pk_disj_concat_left hCP hCO hPO
  have h43Orb : ((rCore.concat rPartner18 hCP).compose sel43Reg).DisjointWires rOrbit16 :=
    QRegister.disjoint_iff.mpr fun i j heq ↦ hActOrb.ne (sel43Reg i) j heq
  have hCombHold : (rCombPack162 (by omega : 138 ≤ mClean) rCore rPartner18 rClean hCP hCW
      hPW).DisjointWires
      (rHold14 hmClean rClean) := by
    dsimp only [rCombPack162, rHold14]
    exact pk_disj_concat_left _ (pk_disj_concat_left _ (h43Clean.compose_right _)
      (pk_slice_disjoint rClean (by omega) (by omega) (Or.inr (by omega))))
      (pk_slice_disjoint rClean (by omega) (by omega) (Or.inr (by omega)))
  have hCombOrb : (rCombPack162 (by omega : 138 ≤ mClean) rCore rPartner18 rClean hCP hCW
      hPW).DisjointWires rOrbit16 := by
    dsimp only [rCombPack162]
    exact pk_disj_concat_left _ (pk_disj_concat_left _ h43Orb (QRegister.disjoint_iff.mpr fun
      i j heq ↦ hOW.ne j _ heq.symm))
      (QRegister.disjoint_iff.mpr fun i j heq ↦ hOW.ne j _ heq.symm)
  exact
    (QRegExt.disjointWires_symm
    (pk_disj_concat_left _ (QRegExt.disjointWires_symm hCombHold)
    (QRegExt.disjointWires_symm hCombOrb)))
/-- `30`-bit combined `(packVWBits14 V W, U, 0)` vector. -/
def packBits30 (U V W : Fin 7 → ZMod 2) (k : Fin 30) : ZMod 2 :=
  if hk : k.val < 14 then packVWBits14 V W ⟨k.val, hk⟩
  else if hu : k.val < 21 then U ⟨k.val - 14, by omega⟩
  else 0
/-- Auxiliary definition `packCanon30`. -/
def packCanon30 (c : CanonicalTriple65) : Fin 30 → ZMod 2 :=
  packBits30 (fin65Bits7 c.u) (fin65Bits7 c.v) (fin65Bits7 c.w)
theorem packCanon30_hold (c : CanonicalTriple65) (k : Fin 14) :
    packCanon30 c (Fin.castAdd 16 k) = packCanonVW14 c k := by
  dsimp only [packCanon30, packBits30, packCanonVW14]
  have hk : (Fin.castAdd 16 k).val < 14 := k.isLt
  rw [pkDitePos hk]
  rfl
theorem packCanon30_orb (c : CanonicalTriple65) (j : Fin 16) : packCanon30 c (Fin.natAdd 14 j)
    = if hj : j.val < 7 then fin65Bits7 c.u ⟨j.val, hj⟩ else 0 := by
  dsimp only [packCanon30, packBits30]
  have hn13 : ¬ (Fin.natAdd 14 j).val < 14 := by dsimp; omega
  rw [pkDiteNeg hn13]
  by_cases hj : j.val < 7
  · have hu : (Fin.natAdd 14 j).val < 21 := by dsimp; omega
    rw [pkDitePos hu, pkDitePos hj]
    exact congrArg (fin65Bits7 c.u) (Fin.ext (by dsimp; omega))
  · have hnu : ¬ (Fin.natAdd 14 j).val < 21 := by dsimp; omega
    rw [pkDiteNeg hnu, pkDiteNeg hj]
theorem bitsVal_packCanon30_orb (c : CanonicalTriple65) :
    bitsVal (fun j : Fin 16 ↦ packCanon30 c (Fin.natAdd 14 j)) = c.u.val := by
  have hfn : (fun j : Fin (7 + 9) ↦ packCanon30 c (Fin.natAdd 14 j)) = fun j : Fin (7 + 9) ↦
      if hj : j.val < 7 then fin65Bits7 c.u ⟨j.val, hj⟩ else 0 := funext (packCanon30_orb c)
  change bitsVal (fun j : Fin (7 + 9) ↦ packCanon30 c (Fin.natAdd 14 j)) = c.u.val
  rw [hfn]
  exact (bitsVal_padZeroRight (W := 7) (K := 9) (fin65Bits7 c.u)).trans (fin65Bits7_val c.u)
/-- Source wires in `rCombPack162` XORed into each bit of `rTarget30` (`14` raw `(V, W)` bits + `7`
  `U` bits). -/
def packSrcIdxs30 (k : Fin 30) : List (Wire 162) :=
  match k.val with
  | 0 => [v7W162 0]
  | 1 => [v7W162 1]
  | 2 => [v7W162 2]
  | 3 => [v7W162 3]
  | 4 => [v7W162 4]
  | 5 => [w7W162 0]
  | 6 => [w7W162 1]
  | 7 => [w7W162 2]
  | 8 => [w7W162 3]
  | 9 => [w7W162 4]
  | 10 => [v7W162 5]
  | 11 => [w7W162 5]
  | 12 => [w7W162 6]
  | 13 => [v7W162 6]
  | 14 => [u7W162 0]
  | 15 => [u7W162 1]
  | 16 => [u7W162 2]
  | 17 => [u7W162 3]
  | 18 => [u7W162 4]
  | 19 => [u7W162 5]
  | 20 => [u7W162 6]
  | _ => []
theorem xorListVal162_packSrcIdxs30 {n : ℕ} (rComb : QRegister 162 n) (δ : BitAssignment n)
    (k : Fin 30) : xorListVal162 rComb δ (packSrcIdxs30 k) = packBits30
    (fun j ↦ δ (rComb (u7W162 j))) (fun j ↦ δ (rComb (v7W162 j)))
    (fun j ↦ δ (rComb (w7W162 j))) k := by
  fin_cases k <;> simp [packSrcIdxs30, xorListVal162, packBits30, packVWBits14, add_zero]
/-- Auxiliary definition `cnotPack30Prefix`. -/
def cnotPack30Prefix {n : ℕ} (rComb : QRegister 162 n) (rT30 : QRegister 30 n)
    (hDisj : rComb.DisjointWires rT30) : (m : ℕ) → m ≤ 30 → Circuit n
  | 0, _ => .identity
  | m + 1, hm =>
      cnotPack30Prefix rComb rT30 hDisj m (by omega) ;;ᶜ
        cnotSingleTgt162 rComb (rT30 ⟨m, hm⟩) (fun idx ↦ hDisj.ne idx ⟨m, hm⟩) (packSrcIdxs30 ⟨m,
            hm⟩)
/-- Auxiliary definition `cPackXor30`. -/
def cPackXor30 {n : ℕ} (rComb : QRegister 162 n) (rT30 : QRegister 30 n)
    (hDisj : rComb.DisjointWires rT30) : Circuit n :=
  cnotPack30Prefix rComb rT30 hDisj 30 le_rfl
theorem count_cPackXor30_toff {n : ℕ} (rComb : QRegister 162 n) (rT30 : QRegister 30 n)
    (hDisj : rComb.DisjointWires rT30) : (cPackXor30 rComb rT30 hDisj).count TOFF = 0 := by
  have hgen : ∀ (m : ℕ) (hm : m ≤ 30),
      (cnotPack30Prefix rComb rT30 hDisj m hm).count TOFF = 0 := by
    intro m; induction m with
    | zero => intro _; rfl
    | succ m ih => intro hm; simp [cnotPack30Prefix, ih (by omega), count_cnotSingleTgt162_toff]
  exact hgen 30 le_rfl
theorem count_cPackXor30_t {n : ℕ} (rComb : QRegister 162 n) (rT30 : QRegister 30 n)
    (hDisj : rComb.DisjointWires rT30) : (cPackXor30 rComb rT30 hDisj).count T = 0 := by
  have hgen : ∀ (m : ℕ) (hm : m ≤ 30),
      (cnotPack30Prefix rComb rT30 hDisj m hm).count T = 0 := by
    intro m; induction m with
    | zero => intro _; rfl
    | succ m ih => intro hm; simp [cnotPack30Prefix, ih (by omega), count_cnotSingleTgt162_t]
  exact hgen 30 le_rfl
/-- Auxiliary definition `packStep30_0`. -/
noncomputable def packStep30_0 {n : ℕ} (rComb : QRegister 162 n) (rT30 : QRegister 30 n)
    (δ : BitAssignment n) : BitAssignment n := fun w ↦ if hk : ∃ k : Fin 30, w = rT30 k then δ
    w + packBits30 (fun j ↦ δ (rComb (u7W162 j))) (fun j ↦ δ (rComb (v7W162 j)))
    (fun j ↦ δ (rComb (w7W162 j))) hk.choose else δ w
theorem packStep30_0_fix_comb {n : ℕ} (rComb : QRegister 162 n) (rT30 : QRegister 30 n)
    (hDisj : rComb.DisjointWires rT30) (δ : BitAssignment n) (idx : Wire 162) : packStep30_0
    rComb rT30 δ (rComb idx) = δ (rComb idx) := pkDiteNeg fun ⟨k, hk⟩ ↦ hDisj.ne idx k hk
theorem eval_cPackXor30_ket {n : ℕ} (rComb : QRegister 162 n) (rT30 : QRegister 30 n)
    (hDisj : rComb.DisjointWires rT30) (δ : BitAssignment n) :
    (cPackXor30 rComb rT30 hDisj).eval.1.mulVec (ket δ) = ket (packStep30_0 rComb rT30 δ) := by
  let stepPfx : ℕ → BitAssignment n := fun m w ↦ if hk : ∃ k : Fin 30, k.val < m ∧ w = rT30 k
      then δ w + xorListVal162 rComb δ (packSrcIdxs30 hk.choose) else δ w
  have hgen : ∀ (m : ℕ) (hm : m ≤ 30),
      (cnotPack30Prefix rComb rT30 hDisj m hm).eval.1.mulVec (ket δ) = ket (stepPfx m) := by
    intro m; induction m with
    | zero =>
        intro _
        have h0 : stepPfx 0 = δ := by
          funext w; dsimp only [stepPfx]
          exact pkDiteNeg fun ⟨k, hlt, _⟩ ↦ Nat.not_lt_zero k.val hlt
        simp [cnotPack30Prefix, h0]
    | succ m ih =>
        intro hm
        dsimp only [cnotPack30Prefix]
        rw [eval_seq_mulVec, ih (by omega), eval_cnotSingleTgt162_ket]
        have hcomb : ∀ u : Wire 162, stepPfx m (rComb u) = δ (rComb u) :=
          fun u ↦ pkDiteNeg fun ⟨k, _, hk⟩ ↦ hDisj.ne u k hk
        rw [xorListVal162_congr rComb hcomb (packSrcIdxs30 ⟨m, hm⟩)]
        have hnot_m : ¬ ∃ k : Fin 30, k.val < m ∧ rT30 ⟨m, hm⟩ = rT30 k := by
          rintro ⟨k, hlt, heq⟩
          have hv := congrArg Fin.val (rT30.wires.injective heq)
          dsimp at hv; omega
        have hbase_m : stepPfx m (rT30 ⟨m, hm⟩) = δ (rT30 ⟨m, hm⟩) := pkDiteNeg hnot_m
        congr 1; funext w
        by_cases hw : w = rT30 ⟨m, hm⟩
        · subst hw
          have hex : ∃ k : Fin 30, k.val < m + 1 ∧ rT30 ⟨m, hm⟩ = rT30 k :=
            ⟨⟨m, hm⟩, Nat.lt_succ_self m, rfl⟩
          have hch : hex.choose = ⟨m, hm⟩ := (rT30.wires.injective hex.choose_spec.2).symm
          rw [Function.update_self, hbase_m]
          dsimp only [stepPfx]
          rw [pkDitePos hex, hch]
        · rw [Function.update_of_ne hw]
          by_cases hk : ∃ k : Fin 30, k.val < m ∧ w = rT30 k
          · have hk1 : ∃ k : Fin 30, k.val < m + 1 ∧ w = rT30 k :=
              ⟨hk.choose, Nat.lt_succ_of_lt hk.choose_spec.1, hk.choose_spec.2⟩
            have hch : hk1.choose = hk.choose :=
              rT30.wires.injective (hk1.choose_spec.2.symm.trans hk.choose_spec.2)
            dsimp only [stepPfx]
            rw [pkDitePos hk, pkDitePos hk1, hch]
          · have hnk1 : ¬ ∃ k : Fin 30, k.val < m + 1 ∧ w = rT30 k := by
              rintro ⟨k, hlt, heq⟩
              by_cases hkm : k.val = m
              · exact hw (heq.trans (congrArg rT30 (Fin.ext hkm)))
              · exact hk ⟨k, by omega, heq⟩
            dsimp only [stepPfx]
            rw [pkDiteNeg hk, pkDiteNeg hnk1]
  dsimp only [cPackXor30]
  rw [hgen 30 le_rfl]
  congr 1; funext w
  by_cases hk : ∃ k : Fin 30, w = rT30 k
  · have hk30 : ∃ k : Fin 30, k.val < 30 ∧ w = rT30 k := ⟨hk.choose, hk.choose.isLt, hk.choose_spec⟩
    have hch : hk30.choose = hk.choose :=
      rT30.wires.injective (hk30.choose_spec.2.symm.trans hk.choose_spec)
    dsimp only [stepPfx, packStep30_0]
    rw [pkDitePos hk30, pkDitePos hk, hch, xorListVal162_packSrcIdxs30]
  · have hnk30 : ¬ ∃ k : Fin 30, k.val < 30 ∧ w = rT30 k := fun ⟨k, _, heq⟩ ↦ hk ⟨k, heq⟩
    dsimp only [stepPfx, packStep30_0]
    rw [pkDiteNeg hnk30, pkDiteNeg hk]
/-- `380 T`, `0` `TOFF` pack/unpack involution XORing `packCanon30` into `rHold14 ++ rOrbit16`
  (`95` `TempAnd`s). -/
def dPack14 {Var : Type} {n mClean : ℕ} (hmClean : 140 ≤ mClean) (slot2SwappedTo0 : Bool)
    (v : Var) (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean) :
    DynamicCircuit Var n :=
  let rComb := rCombPack162 (by omega : 138 ≤ mClean) rCore rPartner18 rClean hCP hCW hPW
  let rT30 := rTarget30 hmClean rOrbit16 rClean hOW
  have hDisj := rCombPack162_disj_target30 hmClean rCore rPartner18 rOrbit16 rClean
    hCP hCO hCW hPO hPW hOW
  toDynWithDyn v rComb (.circuit (cPackXor30 rComb rT30 hDisj)) (packCtx162 slot2SwappedTo0)
theorem count_dPack14_toff {Var : Type} {n mClean : ℕ} (hmClean : 140 ≤ mClean)
    (slot2SwappedTo0 : Bool) (v : Var) (rCore : QRegister posCoreWires n)
    (rPartner18 : QRegister 18 n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean) :
    (dPack14 hmClean slot2SwappedTo0 v rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO
    hPW hOW).count TOFF = 0 := by
  dsimp only [dPack14]
  refine toDynWithDyn_count_toff v _ _ ?_ _
  simp [DynamicCircuit.count, count_cPackXor30_toff]
theorem count_dPack14_t {Var : Type} {n mClean : ℕ} (hmClean : 140 ≤ mClean)
    (slot2SwappedTo0 : Bool) (v : Var) (rCore : QRegister posCoreWires n)
    (rPartner18 : QRegister 18 n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean) :
    (dPack14 hmClean slot2SwappedTo0 v rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO
    hPW hOW).count T = 380 := by
  dsimp only [dPack14]
  rw [toDynWithDyn_count_t, packCtx162_countTempAnd]
  simp only [DynamicCircuit.count, count_cPackXor30_t]
/-- Auxiliary definition `SMid14`. -/
def SMid14 {n mClean : ℕ} (hmClean : 140 ≤ mClean) (rClean : QRegister mClean n)
    (β : BitAssignment n) : Prop :=
  ∀ j : Fin (mClean - 14), β (rCleanMid14 hmClean rClean j) = 0
/-- Auxiliary definition `packStep30`. -/
noncomputable def packStep30 {n : ℕ} (slot2SwappedTo0 : Bool)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n) (rT30 : QRegister 30 n)
    (β : BitAssignment n) : BitAssignment n := fun w ↦ if hk : ∃ k : Fin 30, w = rT30 k then β
    w + packCanon30 (canonTriple128 (rawOrbitCoord128 slot2SwappedTo0 (fun i ↦ β (rCore i))
    (fun i ↦ β (rPartner18 i)))) hk.choose else β w
theorem packStep30_apply_target {n : ℕ} (slot2SwappedTo0 : Bool)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n) (rT30 : QRegister 30 n)
    (β : BitAssignment n) (k : Fin 30) : packStep30 slot2SwappedTo0 rCore rPartner18 rT30 β
    (rT30 k) = β (rT30 k) + packCanon30 (canonTriple128 (rawOrbitCoord128 slot2SwappedTo0 (fun
    i ↦ β (rCore i)) (fun i ↦ β (rPartner18 i)))) k := by
  have hk : ∃ j : Fin 30, rT30 k = rT30 j := ⟨k, rfl⟩
  have hch : hk.choose = k := (rT30.wires.injective hk.choose_spec).symm
  dsimp only [packStep30]
  rw [pkDitePos hk, hch]
theorem packStep30_apply_of_not_target {n : ℕ} (slot2SwappedTo0 : Bool)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n) (rT30 : QRegister 30 n)
    (β : BitAssignment n) {w : Fin n} (hw : ∀ k : Fin 30, w ≠ rT30 k) : packStep30
    slot2SwappedTo0 rCore rPartner18 rT30 β w = β w := pkDiteNeg fun ⟨k, hk⟩ ↦ hw k hk
theorem packStep30_invol {n : ℕ} (slot2SwappedTo0 : Bool) (rCore : QRegister posCoreWires n)
    (rPartner18 : QRegister 18 n) (rT30 : QRegister 30 n) (hCT : rCore.DisjointWires rT30)
    (hPT : rPartner18.DisjointWires rT30) (β : BitAssignment n) : packStep30 slot2SwappedTo0
    rCore rPartner18 rT30 (packStep30 slot2SwappedTo0 rCore rPartner18 rT30 β) = β := by
  let β₁ := packStep30 slot2SwappedTo0 rCore rPartner18 rT30 β
  have hc_eq : (fun i ↦ β₁ (rCore i)) = fun i ↦ β (rCore i) :=
    funext fun i ↦ packStep30_apply_of_not_target _ _ _ _ _ (fun k ↦ hCT.ne i k)
  have hp_eq : (fun i ↦ β₁ (rPartner18 i)) = fun i ↦ β (rPartner18 i) :=
    funext fun i ↦ packStep30_apply_of_not_target _ _ _ _ _ (fun k ↦ hPT.ne i k)
  funext w
  by_cases hk : ∃ k : Fin 30, w = rT30 k
  · obtain ⟨k, rfl⟩ := hk
    rw [packStep30_apply_target, hc_eq, hp_eq, packStep30_apply_target]
    exact CharTwo.add_cancel_right _ _
  · have hnw : ∀ k : Fin 30, w ≠ rT30 k := fun k h ↦ hk ⟨k, h⟩
    rw [packStep30_apply_of_not_target _ _ _ _ _ hnw, packStep30_apply_of_not_target _ _ _ _ _ hnw]
theorem rCleanMid14_disj_target30 {n mClean : ℕ} (hmClean : 140 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) :
    (rCleanMid14 hmClean rClean).DisjointWires (rTarget30 hmClean rOrbit16 rClean hOW) := by
  have hMH : (rCleanMid14 hmClean rClean).DisjointWires (rHold14 hmClean rClean) :=
    pk_slice_disjoint rClean (by omega) (by omega) (Or.inr (by omega))
  have hMO : (rCleanMid14 hmClean rClean).DisjointWires rOrbit16 :=
    QRegister.disjoint_iff.mpr fun i j heq ↦ hOW.ne j _ heq.symm
  exact
    (QRegExt.disjointWires_symm
    (pk_disj_concat_left _ (QRegExt.disjointWires_symm hMH) (QRegExt.disjointWires_symm hMO)))
theorem packStep30_preserves_mid14 {n mClean : ℕ} (hmClean : 140 ≤ mClean)
    (slot2SwappedTo0 : Bool)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean)
    {β : BitAssignment n} (hβ : SMid14 hmClean rClean β) :
    SMid14 hmClean rClean
      (packStep30 slot2SwappedTo0 rCore rPartner18 (rTarget30 hmClean rOrbit16 rClean hOW) β) :=
          fun j ↦ by
  have hdisj := rCleanMid14_disj_target30 hmClean rOrbit16 rClean hOW
  rw [packStep30_apply_of_not_target _ _ _ _ _ (fun k ↦ hdisj.ne j k)]
  exact hβ j
theorem dPack14_constClean {Var : Type} [Fintype Var] [DecidableEq Var] {n mClean : ℕ}
    (hmClean : 140 ≤ mClean) (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean) : ∃ U_pack :
    Unitary (2 ^ n), p2t_RealizesConstCleanUnitary (p2t_ketPredProj (SMid14 hmClean rClean))
    (dPack14 hmClean slot2SwappedTo0 v rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO
    hPW hOW) U_pack ∧ ∀ β : BitAssignment n, SMid14 hmClean rClean β → U_pack.1.mulVec (ket β)
    = ket (packStep30 slot2SwappedTo0 rCore rPartner18 (rTarget30 hmClean rOrbit16 rClean hOW)
    β) := by
  let rComb := rCombPack162 (by omega : 138 ≤ mClean) rCore rPartner18 rClean hCP hCW hPW
  let rT30 := rTarget30 hmClean rOrbit16 rClean hOW
  have hDisj := rCombPack162_disj_target30 hmClean rCore rPartner18 rOrbit16 rClean
    hCP hCO hCW hPO hPW hOW
  let cXor := cPackXor30 rComb rT30 hDisj
  obtain ⟨hv162, hbits162, hfwd162⟩ := packCtx162_spec slot2SwappedTo0
  obtain ⟨U_pack, hReal103, hKet103⟩ := constClean_toDynWithDyn_perm v rComb 0
      (Nat.zero_le 162) (.z wZero162) (fun _ _ ↦ Nat.zero_le _) (fun _ ↦ rfl) (.circuit cXor)
      cXor.eval (p2t_RealizesConstCleanUnitary_circuit _ cXor) (packStep30_0 rComb rT30)
      (packStep30_0_fix_comb rComb rT30 hDisj) (eval_cPackXor30_ket rComb rT30 hDisj)
      (packCtx162 slot2SwappedTo0) 103 (by decide) hv162
  have hSubProj : projZeroAll 103 (tailScr rComb 103 (by decide)) *
      p2t_ketPredProj (SMid14 hmClean rClean) = p2t_ketPredProj (SMid14 hmClean rClean) :=
    pk_projZeroAll_mul_ketPredProj _ fun β hs j ↦ by
      rw [rCombPack162_tailScr103 (by omega : 138 ≤ mClean) rCore rPartner18 rClean hCP hCW hPW j]
      have hj : (⟨34 + j.val, by omega⟩ : Fin mClean) =
          ⟨14 + (20 + j.val), by omega⟩ := by ext; dsimp; omega
      rw [hj]
      exact hs ⟨20 + j.val, by omega⟩
  refine ⟨U_pack, p2t_RealizesConstCleanUnitary_mono_proj (projZeroAll_conjTranspose 103 _)
    (p2t_ketPredProj_conjTranspose _) hSubProj hReal103, fun β hs ↦ ?_⟩
  rw [hKet103 β]
  let γ : BitAssignment 162 := fun idx ↦ β (rComb idx)
  have hcl162 : cleanRem 162 103 γ := fun u hu ↦ by
    have hu_eq : u = ⟨(162 - 103) + (u.val - 59), by omega⟩ := by ext; dsimp; omega
    dsimp only [γ]
    rw [hu_eq]
    change β (tailScr rComb 103 (by decide) ⟨u.val - 59, by omega⟩) = 0
    rw [rCombPack162_tailScr103 (by omega : 138 ≤ mClean) rCore rPartner18 rClean hCP hCW hPW]
    have hj : (⟨34 + (u.val - 59), by omega⟩ : Fin mClean) =
        ⟨14 + (20 + (u.val - 59)), by omega⟩ := by ext; dsimp; omega
    rw [hj]
    exact hs ⟨20 + (u.val - 59), by omega⟩
  have hev : ((packCtx162 slot2SwappedTo0).plug (.z wZero162)).evalBits γ = γ :=
    hbits162 γ hcl162
  obtain ⟨hu7, hv7, hw7⟩ := hfwd162 γ hcl162
  have hcoord := rawOrbitCoord128_rCombPack162 slot2SwappedTo0 (by omega : 138 ≤ mClean)
    rCore rPartner18 rClean hCP hCW hPW β
  let δ := writeRegProg β rComb ((packCtx162 slot2SwappedTo0).fwdBits γ)
  have hδ_u : (fun j ↦ δ (rComb (u7W162 j))) = fin65Bits7 (canonTriple128 (rawOrbitCoord128
      slot2SwappedTo0 (fun i ↦ β (rCore i)) (fun i ↦ β (rPartner18 i)))).u := by
    funext j; dsimp only [δ]
    rw [writeRegProg_apply_reg, hu7 j, hcoord]
  have hδ_v : (fun j ↦ δ (rComb (v7W162 j))) = fin65Bits7 (canonTriple128 (rawOrbitCoord128
      slot2SwappedTo0 (fun i ↦ β (rCore i)) (fun i ↦ β (rPartner18 i)))).v := by
    funext j; dsimp only [δ]
    rw [writeRegProg_apply_reg, hv7 j, hcoord]
  have hδ_w : (fun j ↦ δ (rComb (w7W162 j))) = fin65Bits7 (canonTriple128 (rawOrbitCoord128
      slot2SwappedTo0 (fun i ↦ β (rCore i)) (fun i ↦ β (rPartner18 i)))).w := by
    funext j; dsimp only [δ]
    rw [writeRegProg_apply_reg, hw7 j, hcoord]
  rw [hev]
  congr 1; funext w
  by_cases hm : w ∈ Set.range rComb.wires
  · obtain ⟨idx, rfl⟩ := hm
    rw [writeRegProg_apply_reg,
      packStep30_apply_of_not_target _ _ _ _ _ (fun k ↦ hDisj.ne idx k)]
  · rw [writeRegProg_apply_of_not_mem _ _ _ _ hm]
    have hδw : δ w = β w := writeRegProg_apply_of_not_mem _ _ _ _ hm
    dsimp only [δ, γ] at hδw hδ_u hδ_v hδ_w
    dsimp only [packStep30_0, packStep30, packCanon30]
    by_cases hk : ∃ k : Fin 30, w = rT30 k
    · rw [pkDitePos hk, pkDitePos hk, hδw, hδ_u, hδ_v, hδ_w]
    · rw [pkDiteNeg hk, pkDiteNeg hk, hδw]
attribute [irreducible] dPack14
theorem vwLutAddOpt143_fwd :
    (∀ q : Wire 143, ScopedBlock 143 111 (probeFwd vwLutAddOpt143)
      (.z q) (vwLutAddOpt143.plug (.z q))) ∧
    (∀ (β : BitAssignment 143) (c : CanonicalTriple65),
      cleanRem 143 111 β →
      β wZero143 = 0 →
      (∀ k : Fin 12, β (wPack143 k) = packCanonVW14 c (Fin.castAdd 2 k)) →
      β wW6_143 = packCanonVW14 c ⟨12, by decide⟩ →
      β wV6_143 = packCanonVW14 c ⟨13, by decide⟩ →
      bitsVal (fun k : Fin 16 ↦ vwLutAddOpt143.fwdBits β (outVW16_143 k)) +
        (vwLutAddOpt143.fwdBits β (tet16W143 0)).val =
        triNum c.v.val + tetNum c.w.val) := by
  have hMain : ∀ q₀ : Wire 143,
      ∃ sTail : BitAssignment 143 → BitAssignment 143,
        ScopedBlock 143 111 sTail (.z q₀) (vwLutAddOpt143.plug (.z q₀)) ∧
        ∀ (β : BitAssignment 143) (c : CanonicalTriple65),
          cleanRem 143 111 β →
          β wZero143 = 0 →
          (∀ k : Fin 12, β (wPack143 k) = packCanonVW14 c (Fin.castAdd 2 k)) →
          β wW6_143 = packCanonVW14 c ⟨12, by decide⟩ →
          β wV6_143 = packCanonVW14 c ⟨13, by decide⟩ →
          (∀ j : Fin 16, sTail β (outVW16_143 j) = basisBits 16 (outVWVal c) j) ∧
          sTail β (tet16W143 0) = tetBit0 c := by
    intro q₀
    obtain ⟨sTail, hTail, hSpecTail⟩ := vwLutAddOpt143_block q₀
    refine ⟨sTail, hTail, fun β c hβ hz0 hpack12 hpackW6 hpackV6 ↦ ?_⟩
    have hv_eq : (fun k : Fin 7 ↦ β (v7W143 k)) = fin65Bits7 c.v := by
      funext k; fin_cases k
      · exact hpack12 0
      · exact hpack12 1
      · exact hpack12 2
      · exact hpack12 3
      · exact hpack12 4
      · exact hpack12 10
      · exact hpackV6
    have hw_eq : (fun k : Fin 7 ↦ β (w7W143 k)) = fin65Bits7 c.w := by
      funext k; fin_cases k
      · exact hpack12 5
      · exact hpack12 6
      · exact hpack12 7
      · exact hpack12 8
      · exact hpack12 9
      · exact hpack12 11
      · exact hpackW6
    exact hSpecTail β c hβ hz0 (hv_eq ▸ fin65Bits7_val c.v) (hw_eq ▸ fin65Bits7_val c.w)
  refine ⟨scopedBlock_probeFwd vwLutAddOpt143
      (fun q ↦ let ⟨s, h, _⟩ := hMain q; ⟨s, h⟩),
    fun β c hβ hz0 hpack12 hpackW6 hpackV6 ↦ ?_⟩
  have hOut : (fun k : Fin 16 ↦ vwLutAddOpt143.fwdBits β (outVW16_143 k)) =
      basisBits 16 (outVWVal c) := by
    funext j
    obtain ⟨s_j, h_j, hval_j⟩ := hMain (outVW16_143 j)
    exact (vwLutAddOpt143.plug_evalSign (.z (outVW16_143 j)) β).symm.trans
      ((h_j.sign β hβ).trans ((hval_j β c hβ hz0 hpack12 hpackW6 hpackV6).1 j))
  have hCin : vwLutAddOpt143.fwdBits β (tet16W143 0) = tetBit0 c := by
    obtain ⟨s_0, h_0, hval_0⟩ := hMain (tet16W143 0)
    exact (vwLutAddOpt143.plug_evalSign (.z (tet16W143 0)) β).symm.trans
      ((h_0.sign β hβ).trans (hval_0 β c hβ hz0 hpack12 hpackW6 hpackV6).2)
  rw [hOut, bitsVal_basisBits, hCin]
  dsimp only [outVWVal]
  have hle := (tetBit0_le_vw c).1
  omega
/-- `143`-wire register layout for zero-unpacker `Unpacked14` (`140 ≤ mClean`):
`[0..12) ↦ rClean[0..12)`, `[12..28) ↦ rOrbit16`, `28 ↦ rClean[14]`, `29 ↦ rClean[12]`,
`30 ↦ rClean[15]`, `31 ↦ rClean[13]`, `[32..143) ↦ rClean[16..127)`. -/
def rCombTail14_143 {n mClean : ℕ} (hmClean : 140 ≤ mClean) (rOrbit16 : QRegister 16 n)
    (rClean : QRegister mClean n) (hOW : rOrbit16.DisjointWires rClean) : QRegister 143 n :=
  let rH12 := rClean.slice 0 12 (by omega)
  have hH12O : rH12.DisjointWires rOrbit16 :=
    QRegister.disjoint_iff.mpr fun i j heq ↦ by
      dsimp only [rH12] at heq; rw [QRegister.slice_apply] at heq
      exact hOW.ne j _ heq.symm
  let r28 := rH12.concat rOrbit16 hH12O
  let rZ1 := rClean.slice 14 1 (by omega)
  let rW6_1 := rClean.slice 12 1 (by omega)
  let rT2_1 := rClean.slice 15 1 (by omega)
  let rV6_1 := rClean.slice 13 1 (by omega)
  let rScr111 := rClean.slice 16 111 (by omega)
  have h28Z1 : r28.DisjointWires rZ1 :=
    pk_disj_concat_left hH12O
      (pk_slice_disjoint rClean (by omega) (by omega) (Or.inl (by omega)))
      (QRegister.disjoint_iff.mpr fun i j heq ↦ hOW.ne i ⟨14 + j.val, by omega⟩ heq)
  let r29 := r28.concat rZ1 h28Z1
  have h29W6 : r29.DisjointWires rW6_1 :=
    pk_disj_concat_left h28Z1
      (pk_disj_concat_left hH12O
        (pk_slice_disjoint rClean (by omega) (by omega) (Or.inl (by omega)))
        (QRegister.disjoint_iff.mpr fun i j heq ↦ hOW.ne i ⟨12 + j.val, by omega⟩ heq))
      (pk_slice_disjoint rClean (by omega) (by omega) (Or.inr (by omega)))
  let r30 := r29.concat rW6_1 h29W6
  have h30T2 : r30.DisjointWires rT2_1 :=
    pk_disj_concat_left h29W6
      (pk_disj_concat_left h28Z1
        (pk_disj_concat_left hH12O
          (pk_slice_disjoint rClean (by omega) (by omega) (Or.inl (by omega)))
          (QRegister.disjoint_iff.mpr fun i j heq ↦ hOW.ne i ⟨15 + j.val, by omega⟩ heq))
        (pk_slice_disjoint rClean (by omega) (by omega) (Or.inl (by omega))))
      (pk_slice_disjoint rClean (by omega) (by omega) (Or.inl (by omega)))
  let r31 := r30.concat rT2_1 h30T2
  have h31V6 : r31.DisjointWires rV6_1 :=
    pk_disj_concat_left h30T2
      (pk_disj_concat_left h29W6
        (pk_disj_concat_left h28Z1
          (pk_disj_concat_left hH12O
            (pk_slice_disjoint rClean (by omega) (by omega) (Or.inl (by omega)))
            (QRegister.disjoint_iff.mpr fun i j heq ↦ hOW.ne i ⟨13 + j.val, by omega⟩ heq))
          (pk_slice_disjoint rClean (by omega) (by omega) (Or.inr (by omega))))
        (pk_slice_disjoint rClean (by omega) (by omega) (Or.inl (by omega))))
      (pk_slice_disjoint rClean (by omega) (by omega) (Or.inr (by omega)))
  let r32 := r31.concat rV6_1 h31V6
  have h32S111 : r32.DisjointWires rScr111 :=
    pk_disj_concat_left h31V6
      (pk_disj_concat_left h30T2
        (pk_disj_concat_left h29W6
          (pk_disj_concat_left h28Z1
            (pk_disj_concat_left hH12O
              (pk_slice_disjoint rClean (by omega) (by omega) (Or.inl (by omega)))
              (QRegister.disjoint_iff.mpr fun i j heq ↦ hOW.ne i ⟨16 + j.val, by omega⟩ heq))
            (pk_slice_disjoint rClean (by omega) (by omega) (Or.inl (by omega))))
          (pk_slice_disjoint rClean (by omega) (by omega) (Or.inl (by omega))))
        (pk_slice_disjoint rClean (by omega) (by omega) (Or.inl (by omega))))
      (pk_slice_disjoint rClean (by omega) (by omega) (Or.inl (by omega)))
  r32.concat rScr111 h32S111
theorem rCombTail14_143_pack12 {n mClean : ℕ} (hmClean : 140 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) (k : Fin 12) : rCombTail14_143 hmClean rOrbit16
    rClean hOW (wPack143 k) = rHold14 hmClean rClean (Fin.castAdd 2 k) := by
  have he : (wPack143 k : Fin ((((((12 + 16) + 1) + 1) + 1) + 1) + 111)) =
      Fin.castAdd 111 (Fin.castAdd 1 (Fin.castAdd 1 (Fin.castAdd 1 (Fin.castAdd 1 (Fin.castAdd 16
          k))))) := rfl
  dsimp only [rCombTail14_143, rHold14]
  rw [he, QRegister.concat_apply_left, QRegister.concat_apply_left, QRegister.concat_apply_left,
      QRegister.concat_apply_left, QRegister.concat_apply_left, QRegister.concat_apply_left,
      QRegister.slice_apply, QRegister.slice_apply]
  rfl
theorem rCombTail14_143_w6 {n mClean : ℕ} (hmClean : 140 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) :
    rCombTail14_143 hmClean rOrbit16 rClean hOW wW6_143 =
      rHold14 hmClean rClean ⟨12, by decide⟩ := by
  have he : (wW6_143 : Fin ((((((12 + 16) + 1) + 1) + 1) + 1) + 111)) =
      Fin.castAdd 111 (Fin.castAdd 1 (Fin.castAdd 1 (Fin.natAdd 29 (⟨0, by decide⟩ : Fin 1)))) :=
          rfl
  dsimp only [rCombTail14_143, rHold14]
  rw [he, QRegister.concat_apply_left, QRegister.concat_apply_left, QRegister.concat_apply_left,
      QRegister.concat_apply_right, QRegister.slice_apply, QRegister.slice_apply]
  rfl
theorem rCombTail14_143S6 {n mClean : ℕ} (hmClean : 140 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) :
    rCombTail14_143 hmClean rOrbit16 rClean hOW wV6_143 =
      rHold14 hmClean rClean ⟨13, by decide⟩ := by
  have he : (wV6_143 : Fin ((((((12 + 16) + 1) + 1) + 1) + 1) + 111)) =
      Fin.castAdd 111 (Fin.natAdd 31 (⟨0, by decide⟩ : Fin 1)) := rfl
  dsimp only [rCombTail14_143, rHold14]
  rw [he, QRegister.concat_apply_left, QRegister.concat_apply_right,
      QRegister.slice_apply, QRegister.slice_apply]
  rfl
theorem rCombTail14_143_zero {n mClean : ℕ} (hmClean : 140 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) :
    rCombTail14_143 hmClean rOrbit16 rClean hOW wZero143 =
      rCleanMid14 hmClean rClean ⟨0, by omega⟩ := by
  have he : (wZero143 : Fin ((((((12 + 16) + 1) + 1) + 1) + 1) + 111)) =
      Fin.castAdd 111 (Fin.castAdd 1 (Fin.castAdd 1 (Fin.castAdd 1 (Fin.natAdd 28 (⟨0, by decide⟩ :
          Fin 1))))) := rfl
  dsimp only [rCombTail14_143, rCleanMid14]
  rw [he, QRegister.concat_apply_left, QRegister.concat_apply_left, QRegister.concat_apply_left,
      QRegister.concat_apply_left, QRegister.concat_apply_right,
      QRegister.slice_apply, QRegister.slice_apply]
theorem rCombTail14_143_orb {n mClean : ℕ} (hmClean : 140 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) (j : Fin 16) :
    rCombTail14_143 hmClean rOrbit16 rClean hOW (wOrb143 j) = rOrbit16 j := by
  have he : (wOrb143 j : Fin ((((((12 + 16) + 1) + 1) + 1) + 1) + 111)) =
      Fin.castAdd 111 (Fin.castAdd 1 (Fin.castAdd 1 (Fin.castAdd 1 (Fin.castAdd 1 (Fin.natAdd 12
          j))))) := rfl
  dsimp only [rCombTail14_143]
  rw [he, QRegister.concat_apply_left, QRegister.concat_apply_left, QRegister.concat_apply_left,
      QRegister.concat_apply_left, QRegister.concat_apply_left, QRegister.concat_apply_right]
theorem rCombTail14_143_scr111 {n mClean : ℕ} (hmClean : 140 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) (j : Fin 111) :
    rCombTail14_143 hmClean rOrbit16 rClean hOW ⟨32 + j.val, by omega⟩ =
      rCleanMid14 hmClean rClean ⟨2 + j.val, by omega⟩ := by
  have he : (⟨32 + j.val, by omega⟩ : Fin ((((((12 + 16) + 1) + 1) + 1) + 1) + 111)) =
      Fin.natAdd 32 j := rfl
  dsimp only [rCombTail14_143, rCleanMid14]
  rw [he, QRegister.concat_apply_right, QRegister.slice_apply, QRegister.slice_apply]
  exact congrArg rClean.wires (Fin.ext (by dsimp; omega))
/-! ## Section 1A: Generic `ctxLinAndSteps` Splitting & Support Helpers -/
theorem ctxLinAndSteps_supportsBelowCtx {M : ℕ} :
    ∀ (steps : List (ℕ × ℕ)) (cur : ℕ) (hcur : cur + steps.length ≤ M)
      (scrL scrR : Wire M) (hLR : scrL ≠ scrR)
      (hL_lt : scrL.val < cur) (hR_lt : scrR.val < cur)
      (accW : List (Wire M)) (hacc_lt : ∀ w ∈ accW, w.val < cur)
      (hacc_neL : ∀ w ∈ accW, w ≠ scrL) (hacc_neR : ∀ w ∈ accW, w ≠ scrR),
      (ctxLinAndSteps cur steps hcur scrL scrR hLR hL_lt hR_lt
        accW hacc_lt hacc_neL hacc_neR).SupportsBelowCtx (cur + steps.length)
  | [], _, _, _, _, _, _, _, _, _, _, _ => trivial
  | (ma, mb) :: rest, cur, hcur, scrL, scrR, hLR, hL_lt, hR_lt, accW, hacc_lt, hacc_neL, hacc_neR
      => by
      let anc : Wire M := ⟨cur, by dsimp [List.length] at hcur; omega⟩
      have hcur' : (cur + 1) + rest.length ≤ M := by dsimp [List.length] at hcur; omega
      have hacc_lt' : ∀ w ∈ accW ++ [anc], w.val < cur + 1 := by
        intro w hw
        rcases List.mem_append.mp hw with h1 | h2
        · exact lt_trans (hacc_lt w h1) (by omega)
        · simp only [List.mem_singleton] at h2; subst h2; dsimp [anc]; omega
      have hacc_neL' : ∀ w ∈ accW ++ [anc], w ≠ scrL := by
        intro w hw
        rcases List.mem_append.mp hw with h1 | h2
        · exact hacc_neL w h1
        · simp only [List.mem_singleton] at h2; subst h2; exact wire_ne_of_gt hL_lt
      have hacc_neR' : ∀ w ∈ accW ++ [anc], w ≠ scrR := by
        intro w hw
        rcases List.mem_append.mp hw with h1 | h2
        · exact hacc_neR w h1
        · simp only [List.mem_singleton] at h2; subst h2; exact wire_ne_of_gt hR_lt
      have hsL := xorMaskedList_supportsBelow scrL (cur + 1) (by omega) ma accW hacc_neL
        (fun w hw ↦ lt_trans (hacc_lt w hw) (by omega))
      have hsR := xorMaskedList_supportsBelow scrR (cur + 1) (by omega) mb accW hacc_neR
        (fun w hw ↦ lt_trans (hacc_lt w hw) (by omega))
      have hsRest := ctxLinAndSteps_supportsBelowCtx rest (cur + 1) hcur' scrL scrR hLR
        (lt_trans hL_lt (by omega)) (lt_trans hR_lt (by omega))
        (accW ++ [anc]) hacc_lt' hacc_neL' hacc_neR'
      have heq : (cur + 1) + rest.length = cur + ((ma, mb) :: rest).length := by
        dsimp [List.length]; omega
      rw [← heq]
      dsimp only [ctxLinAndSteps]
      exact TempCtx.supportsBelowCtx_append (Nat.le_add_right _ _)
        (ctxCliffAlloc_supports ⟨hsL, hsR⟩)
        (TempCtx.supportsBelowCtx_append (Nat.le_add_right _ _)
          ⟨by dsimp [anc]; omega, trivial⟩
          (TempCtx.supportsBelowCtx_append (Nat.le_add_right _ _)
            (ctxCliffAlloc_supports ⟨hsR, hsL⟩)
            hsRest))
theorem ctxLinAndSteps_append_aux {M : ℕ} :
    ∀ (s1 s2 : List (ℕ × ℕ)) (cur cur2 : ℕ)
      (hcur1 : cur + s1.length ≤ M) (hcur2 : cur2 + s2.length ≤ M)
      (hcur12 : cur + (s1 ++ s2).length ≤ M)
      (scrL scrR : Wire M) (hLR : scrL ≠ scrR)
      (hL1 : scrL.val < cur) (hR1 : scrR.val < cur)
      (hL2 : scrL.val < cur2) (hR2 : scrR.val < cur2)
      (accW accW2 : List (Wire M))
      (hacc1 : ∀ w ∈ accW, w.val < cur)
      (hneL1 : ∀ w ∈ accW, w ≠ scrL) (hneR1 : ∀ w ∈ accW, w ≠ scrR)
      (hacc2 : ∀ w ∈ accW2, w.val < cur2)
      (hneL2 : ∀ w ∈ accW2, w ≠ scrL) (hneR2 : ∀ w ∈ accW2, w ≠ scrR),
      cur2 = cur + s1.length →
      accW2 = accW ++ ancList cur s1.length hcur1 →
      (ctxLinAndSteps cur s1 hcur1 scrL scrR hLR hL1 hR1 accW hacc1 hneL1 hneR1).append
        (ctxLinAndSteps cur2 s2 hcur2 scrL scrR hLR hL2 hR2 accW2 hacc2 hneL2 hneR2) =
      ctxLinAndSteps cur (s1 ++ s2) hcur12 scrL scrR hLR hL1 hR1 accW hacc1 hneL1 hneR1
  | [], s2, cur, cur2, hcur1, hcur2, hcur12, scrL, scrR, hLR, hL1, hR1, hL2, hR2,
    accW, accW2, hacc1, hneL1, hneR1, hacc2, hneL2, hneR2, hcur_eq, hacc_eq => by
      have hc : cur2 = cur := by dsimp [List.length] at hcur_eq; omega
      have ha : accW2 = accW := by simpa [ancList] using hacc_eq
      subst hc; subst ha
      rfl
  | (ma, mb) :: rest, s2, cur, cur2, hcur1, hcur2, hcur12, scrL, scrR, hLR, hL1, hR1, hL2, hR2,
    accW, accW2, hacc1, hneL1, hneR1, hacc2, hneL2, hneR2, hcur_eq, hacc_eq => by
      dsimp only [ctxLinAndSteps, List.cons_append]
      rw [tempCtx_append_assoc, tempCtx_append_assoc, tempCtx_append_assoc]
      congr 1; congr 1; congr 1
      let anc : Wire M := ⟨cur, by dsimp [List.length] at hcur1; omega⟩
      have hcur1' : (cur + 1) + rest.length ≤ M := by dsimp [List.length] at hcur1; omega
      exact ctxLinAndSteps_append_aux rest s2 (cur + 1) cur2 hcur1' hcur2 _ scrL scrR hLR
        _ _ hL2 hR2 (accW ++ [anc]) accW2 _ _ _ hacc2 hneL2 hneR2
        (by dsimp [List.length] at hcur_eq; omega)
        (by simpa [ancList, anc, List.append_assoc] using hacc_eq)
/-! ## Section 1B: Branch 1 — `12`-Wire Shaved Packed Branch (`1,400 + midK6GuardBaseT B (mClean
- 12)`) -/
/-- Exact base `T`-count (`+ 260 * B`) of the `12`-wire shaved packed branch (`138 ≤ mClean`). -/
def cert12BoothOptBaseT (B mClean : ℕ) : ℕ := 1400 + midK6GuardBaseT B (mClean - 12)
/-- `12`-wire shaved packed `OrbitSand` (`1,400 T` outer) wrapped around
  `dMidK6GuardOptDyn`. -/
noncomputable def dOrbitSandPacked12BoothOptDyn {Var : Type} {n mClean : ℕ} (B : ℕ)
    (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 138 ≤ mClean) (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean) :
    DynamicCircuit Var n := dOrbitSandPacked12Opt mClean hmClean slot2SwappedTo0 v rCore
    rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW (dMidK6GuardOptDyn B hB6 hB27
    (by omega) v rCore rOrbit16 (rClean.slice 12 (mClean - 12) (by omega)) hCO
    (hCW.compose_right _) (hOW.compose_right _))
theorem dOrbitSandPacked12BoothOptDyn_spec {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mClean : ℕ} (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 138 ≤ mClean)
    (slot2SwappedTo0 : Bool) (v : Var) (rCore : QRegister posCoreWires n)
    (rPartner18 : QRegister 18 n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean) :
    (dOrbitSandPacked12BoothOptDyn B hB6 hB27 hmClean slot2SwappedTo0 v rCore rPartner18
    rOrbit16 rClean hCP hCO hCW hPO hPW hOW).count TOFF = 0 ∧ (dOrbitSandPacked12BoothOptDyn B
    hB6 hB27 hmClean slot2SwappedTo0 v rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW
    hOW).count T ≤ cert12BoothOptBaseT B mClean + 260 * B ∧
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (rCore.concat rPartner18 hCP)
    (rOrbit16.concat rClean hOW) (diagSignUnitary (PosSlots24PartnerMux288.sandPhase18
    slot2SwappedTo0 (midPhaseBitSpec slot2SwappedTo0 pos24TailSign (pos24TailMag30MidpointB B
    (by omega) (by omega))))) (dOrbitSandPacked12BoothOptDyn B hB6 hB27 hmClean slot2SwappedTo0
    v rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW) := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [dOrbitSandPacked12BoothOptDyn]
    rw [count_dOrbitSandPacked12Opt_toff, count_dMidK6GuardOptDyn_toff]
  · dsimp only [dOrbitSandPacked12BoothOptDyn, cert12BoothOptBaseT]
    rw [count_dOrbitSandPacked12Opt_t]
    have hMid := count_dMidK6GuardOptDyn_t_le_exact B hB6 hB27 (by omega) v
      rCore rOrbit16 (rClean.slice 12 (mClean - 12) (by omega))
      hCO (hCW.compose_right _) (hOW.compose_right _)
    omega
  · dsimp only [dOrbitSandPacked12BoothOptDyn]
    rw [← sandPhase18_k6MidPhaseBitSpecB_eq B (by omega) (by omega) slot2SwappedTo0]
    exact dOrbitSandPacked12Opt_realizes mClean hmClean slot2SwappedTo0 _ v rCore
      rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW _ (dMidK6GuardOptDyn_realizes B hB6
      hB27 (by omega) slot2SwappedTo0 v rCore rOrbit16 (rClean.slice 12 (mClean - 12)
      (by omega)) hCO (hCW.compose_right _) (hOW.compose_right _))
theorem count_dOrbitSandPacked12BoothOptDyn_toff {Var : Type} {n mClean : ℕ} (B : ℕ)
    (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 138 ≤ mClean) (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean) :
    (dOrbitSandPacked12BoothOptDyn B hB6 hB27 hmClean slot2SwappedTo0 v rCore rPartner18
    rOrbit16 rClean hCP hCO hCW hPO hPW hOW).count TOFF = 0 := by
  dsimp only [dOrbitSandPacked12BoothOptDyn]
  rw [count_dOrbitSandPacked12Opt_toff, count_dMidK6GuardOptDyn_toff]
theorem count_dOrbitSandPacked12BoothOptDyn_t_le {Var : Type} {n mClean : ℕ} (B : ℕ)
    (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 138 ≤ mClean) (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean) :
    (dOrbitSandPacked12BoothOptDyn B hB6 hB27 hmClean slot2SwappedTo0 v rCore rPartner18
    rOrbit16 rClean hCP hCO hCW hPO hPW hOW).count T ≤ cert12BoothOptBaseT B mClean + 260 * B
    := by
  dsimp only [dOrbitSandPacked12BoothOptDyn, cert12BoothOptBaseT]
  rw [count_dOrbitSandPacked12Opt_t]
  have hMid := count_dMidK6GuardOptDyn_t_le_exact B hB6 hB27 (by omega) v
    rCore rOrbit16 (rClean.slice 12 (mClean - 12) (by omega))
    hCO (hCW.compose_right _) (hOW.compose_right _)
  omega
attribute [irreducible] dOrbitSandPacked12BoothOptDyn
theorem triSteps18List_length : triSteps18List.length = 18 := rfl
/-- Post-`triSteps18List` tail context (`43` `TempAnd`s): `triOuts12_18` XORs + `tetLut` (`29`) +
  `14`-bit adder (`14`). -/
def tailAfterTri18_143 : TempCtx 143 :=
  let fullAccV := v7List143 ++ ancList 36 triSteps18List.length (by decide)
  let cOut := writeLinAndOuts fullAccV 12 54 (by decide)
    (fullAccW_lt 34 v7List143 triSteps18List.length (by decide) v7List143_lt34) triOuts12_18
  let s3b := ctxLinAndLut 16 66 w7List143 tetSteps29List tetOuts16 (by decide) w7List143_lt66
  let s3c :=
    ctxAddMod2Pow 14 114 (by decide) triPad15Hi143 tet15HiW143 cinZero143
      (fun i j ↦ wire_ne_of_lt (lt_of_le_of_lt (triPad15Hi143_le65 i)
        (by have := j.isLt; dsimp [tet15HiW143, tet16W143]; omega)))
      (fun i ↦ wire_ne_of_lt (lt_of_le_of_lt (triPad15Hi143_le65 i) (by decide)))
      (fun i ↦ wire_ne_of_lt (by have := i.isLt; dsimp [tet15HiW143, tet16W143, cinZero143]; omega))
      (fun i ↦ lt_of_le_of_lt (triPad15Hi143_le65 i) (by decide))
      (fun i ↦ by have := i.isLt; dsimp [tet15HiW143, tet16W143]; omega)
      (by decide)
  (ctxCliffAlloc cOut).append (s3b.append s3c)
@[simp] theorem tailAfterTri18_143_countTempAnd : tailAfterTri18_143.countTempAnd = 43 := rfl
theorem tailAfterTri18_143_supp128B : ctxSupportsBelowB 128 tailAfterTri18_143 = true := rfl
theorem tailAfterTri18_143_disj_supp : tailAfterTri18_143.DisjointFrom mutOrb143 ∧
    tailAfterTri18_143.SupportsBelowCtx 128 := by
  have hnAcc : ∀ w ∈ v7List143 ++ ancList 36 triSteps18List.length (by decide), ¬ mutOrb143 w := by
    intro w hw
    rcases List.mem_append.mp hw with h1 | h2
    · exact v7List143_not_mut w h1
    · have hb := (ancList_mem_bounds 36 triSteps18List.length (by decide) w h2).1
      exact not_mutOrb143_of_ge28 (by omega)
  have hdOut := writeLinAndOuts_disjoint (mutW := mutOrb143)
    (v7List143 ++ ancList 36 triSteps18List.length (by decide)) hnAcc
    12 54 (by decide)
    (fullAccW_lt 34 v7List143 triSteps18List.length (by decide) v7List143_lt34)
    triOuts12_18 (fun _ hw ↦ not_mutOrb143_of_ge28 (by omega))
  have hd3b := ctxLinAndLut_disj (mutW := mutOrb143) 16 66 w7List143 tetSteps29List tetOuts16
    (by decide) w7List143_lt66 w7List143_not_mut
    (fun _ hw ↦ not_mutOrb143_of_ge28 (by omega))
  obtain ⟨hdAdd, _⟩ := ctxAddMod2Pow_disj_supp (mutW := mutOrb143) 14 114 (by decide)
    triPad15Hi143 tet15HiW143 cinZero143 _ _ _ _ _ _
    triPad15Hi143_not_mut
    (fun i ↦ not_mutOrb143_of_ge28 (by dsimp [tet15HiW143, tet16W143]; omega))
    (not_mutOrb143_of_ge28 (by decide))
    (fun _ hw ↦ not_mutOrb143_of_ge28 (by omega))
  exact ⟨TempCtx.disjointFrom_append (ctxCliffAlloc_disjoint hdOut)
      (TempCtx.disjointFrom_append hd3b hdAdd),
    supportsBelowCtx_of_ctxSupportsBelowB tailAfterTri18_143_supp128B⟩
theorem tailAfterTri18_143_block (q₀ : Wire 143) :
    ∃ sAfter : BitAssignment 143 → BitAssignment 143,
      ScopedBlock 143 (143 - 54) sAfter (.z q₀) (tailAfterTri18_143.plug (.z q₀)) := by
  have hLeaf0 : ScopedBlock 143 (143 - 128) id (.z q₀) (.z q₀) :=
    ⟨trivial, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
  obtain ⟨sAdd, hAdd_0, _⟩ := ScopedBlock.ctxAddMod2Pow_block (M := 143)
    14 114 (by decide) triPad15Hi143 tet15HiW143 cinZero143
    (fun i j ↦ wire_ne_of_lt (lt_of_le_of_lt (triPad15Hi143_le65 i)
      (by have := j.isLt; dsimp [tet15HiW143, tet16W143]; omega)))
    (fun i ↦ wire_ne_of_lt (lt_of_le_of_lt (triPad15Hi143_le65 i) (by decide)))
    (fun i ↦ wire_ne_of_lt (by have := i.isLt; dsimp [tet15HiW143, tet16W143, cinZero143]; omega))
    tet15HiW143_injective
    (fun i ↦ lt_of_le_of_lt (triPad15Hi143_le65 i) (by decide))
    (fun i ↦ by have := i.isLt; dsimp [tet15HiW143, tet16W143]; omega)
    (by decide)
    (.z q₀) (.z q₀) id hLeaf0
  have hAdd : ScopedBlock 143 (143 - 113) sAdd (.z q₀) _ := ⟨pkValidCleanRemUp (by decide)
      hAdd_0.valid, fun β hβ ↦ hAdd_0.bits β (fun u hu ↦ hβ u (by omega)), fun β hβ ↦
      hAdd_0.sign β (fun u hu ↦ hβ u (by omega))⟩
  obtain ⟨sLut2, hLut2, _⟩ := ScopedBlock.ctxLinAndLut_block (M := 143)
    16 66 w7List143 tetSteps29List tetOuts16 (by decide) w7List143_lt66
    (.z q₀) _ sAdd hAdd
  let fullAccV := v7List143 ++ ancList 36 triSteps18List.length (by decide)
  let cOut := writeLinAndOuts fullAccV 12 54 (by decide)
    (fullAccW_lt 34 v7List143 triSteps18List.length (by decide) v7List143_lt34) triOuts12_18
  have hOut := ScopedBlock.withCliffCur (M := 143) (cur := 54) (curIn := 66)
    (by decide) (by decide) cOut
    (writeLinAndOuts_supportsBelow fullAccV 12 54 (by decide)
      (fullAccW_lt 34 v7List143 triSteps18List.length (by decide) v7List143_lt34) triOuts12_18)
    hLut2
  refine ⟨fun β ↦ sAdd (sLut2 (cOut.eval β)), ?_⟩
  dsimp only [tailAfterTri18_143]
  rw [TempCtx.append_plug, TempCtx.append_plug, ctxCliffAlloc_plug]
  exact hOut
theorem v7List143_lt36 : ∀ w ∈ v7List143, w.val < 36 :=
  fun w hw ↦ lt_trans (v7List143_lt34 w hw) (by decide)
theorem v7List143_ne34 : ∀ w ∈ v7List143, w ≠ (⟨34, by decide⟩ : Wire 143) :=
  fun w hw ↦ wire_ne_of_lt (v7List143_lt34 w hw)
theorem v7List143_ne35 : ∀ w ∈ v7List143, w ≠ (⟨35, by decide⟩ : Wire 143) :=
  fun w hw ↦ wire_ne_of_lt (lt_trans (v7List143_lt34 w hw) (by decide))
theorem accWK143_lt (K : ℕ) (hK : K ≤ 18) :
    ∀ w ∈ v7List143 ++ ancList 36 K (by omega), w.val < 36 + K := by
  intro w hw
  rcases List.mem_append.mp hw with h1 | h2
  · exact lt_trans (v7List143_lt34 w h1) (by omega)
  · exact (ancList_mem_bounds 36 K (by omega) w h2).2
theorem accWK143_ne34 (K : ℕ) (hK : K ≤ 18) :
    ∀ w ∈ v7List143 ++ ancList 36 K (by omega), w ≠ (⟨34, by decide⟩ : Wire 143) := by
  intro w hw
  rcases List.mem_append.mp hw with h1 | h2
  · exact v7List143_ne34 w h1
  · have hb := (ancList_mem_bounds 36 K (by omega) w h2).1
    exact wire_ne_of_gt (by dsimp; omega)
theorem accWK143_ne35 (K : ℕ) (hK : K ≤ 18) :
    ∀ w ∈ v7List143 ++ ancList 36 K (by omega), w ≠ (⟨35, by decide⟩ : Wire 143) := by
  intro w hw
  rcases List.mem_append.mp hw with h1 | h2
  · exact v7List143_ne35 w h1
  · have hb := (ancList_mem_bounds 36 K (by omega) w h2).1
    exact wire_ne_of_gt (by dsimp; omega)
/-- Held prefix (`K ≤ 18` `TempAnd`s at wires `36 .. 36 + K - 1`) of `vwLutAddOpt143`. -/
def heldTri18Ctx143 (K : ℕ) (hK : K ≤ 18) : TempCtx 143 :=
  ctxLinAndSteps 36 (triSteps18List.take K)
    (by rw [List.length_take, triSteps18List_length]; omega)
    ⟨34, by decide⟩ ⟨35, by decide⟩ (by decide) (by decide) (by decide)
    v7List143 v7List143_lt36 v7List143_ne34 v7List143_ne35
/-- Remaining suffix (`61 - K` `TempAnd`s) of `vwLutAddOpt143` after holding `K` `triSteps18List`
  pebbles. -/
def remTri18Ctx143 (K : ℕ) (hK : K ≤ 18) : TempCtx 143 :=
  (ctxLinAndSteps (36 + K) (triSteps18List.drop K)
      (by rw [List.length_drop, triSteps18List_length]; omega)
      ⟨34, by decide⟩ ⟨35, by decide⟩ (by decide)
      (by dsimp; omega) (by dsimp; omega)
      (v7List143 ++ ancList 36 K (by omega))
      (accWK143_lt K hK) (accWK143_ne34 K hK) (accWK143_ne35 K hK)).append
    tailAfterTri18_143
@[simp] theorem heldTri18Ctx143_countTempAnd (K : ℕ) (hK : K ≤ 18) :
    (heldTri18Ctx143 K hK).countTempAnd = K := by
  dsimp only [heldTri18Ctx143]
  rw [ctxLinAndSteps_countTempAnd, List.length_take, triSteps18List_length, Nat.min_eq_left hK]
@[simp] theorem remTri18Ctx143_countTempAnd (K : ℕ) (hK : K ≤ 18) :
    (remTri18Ctx143 K hK).countTempAnd = 61 - K := by
  dsimp only [remTri18Ctx143]
  rw [tempCtx_append_count, ctxLinAndSteps_countTempAnd, tailAfterTri18_143_countTempAnd,
    List.length_drop, triSteps18List_length]
  omega
theorem ancList_congr_len {M cur n₁ n₂ : ℕ} (hn : n₁ = n₂) (h₁ : cur + n₁ ≤ M)
    (h₂ : cur + n₂ ≤ M) : ancList cur n₁ h₁ = ancList cur n₂ h₂ := by
  subst hn; rfl
theorem ctxLinAndSteps_congr {M c₁ c₂ : ℕ} {s₁ s₂ : List (ℕ × ℕ)} (hc : c₁ = c₂)
    (hs : s₁ = s₂) (hcur₁ : c₁ + s₁.length ≤ M) (hcur₂ : c₂ + s₂.length ≤ M)
    {L₁ R₁ L₂ R₂ : Wire M} (hL : L₁ = L₂) (hR : R₁ = R₂) (hLR₁ : L₁ ≠ R₁) (hLR₂ : L₂ ≠ R₂)
    (hLlt₁ : L₁.val < c₁) (hRlt₁ : R₁.val < c₁) (hLlt₂ : L₂.val < c₂) (hRlt₂ : R₂.val < c₂)
    {acc₁ acc₂ : List (Wire M)} (hacc : acc₁ = acc₂) (ha₁ : ∀ w ∈ acc₁, w.val < c₁)
    (hneL₁ : ∀ w ∈ acc₁, w ≠ L₁) (hneR₁ : ∀ w ∈ acc₁, w ≠ R₁) (ha₂ : ∀ w ∈ acc₂, w.val < c₂)
    (hneL₂ : ∀ w ∈ acc₂, w ≠ L₂) (hneR₂ : ∀ w ∈ acc₂, w ≠ R₂) : ctxLinAndSteps c₁ s₁ hcur₁ L₁
    R₁ hLR₁ hLlt₁ hRlt₁ acc₁ ha₁ hneL₁ hneR₁ = ctxLinAndSteps c₂ s₂ hcur₂ L₂ R₂ hLR₂ hLlt₂
    hRlt₂ acc₂ ha₂ hneL₂ hneR₂ := by
  subst hc; subst hs; subst hL; subst hR; subst hacc; rfl
theorem heldTri18Ctx143_append_rem (K : ℕ) (hK : K ≤ 18) :
    (heldTri18Ctx143 K hK).append (remTri18Ctx143 K hK) = vwLutAddOpt143 := by
  dsimp only [heldTri18Ctx143, remTri18Ctx143]
  rw [← tempCtx_append_assoc]
  have hlen : (triSteps18List.take K).length = K := by
    rw [List.length_take, triSteps18List_length, Nat.min_eq_left hK]
  have hcat := List.take_append_drop K triSteps18List
  have happ := ctxLinAndSteps_append_aux (M := 143)
    (triSteps18List.take K) (triSteps18List.drop K) 36 (36 + K)
    (by rw [hlen]; omega)
    (by rw [List.length_drop, triSteps18List_length]; omega)
    (by rw [hcat, triSteps18List_length]; decide)
    ⟨34, by decide⟩ ⟨35, by decide⟩ (by decide)
    (by decide) (by decide) (by dsimp; omega) (by dsimp; omega)
    v7List143 (v7List143 ++ ancList 36 K (by omega))
    v7List143_lt36 v7List143_ne34 v7List143_ne35
    (accWK143_lt K hK) (accWK143_ne34 K hK) (accWK143_ne35 K hK)
    (by rw [hlen])
    (congrArg (v7List143 ++ ·) (ancList_congr_len hlen.symm _ _))
  rw [happ]
  dsimp only [vwLutAddOpt143, tailAfterTri18_143]
  have hs3a : ctxLinAndLut 12 34 v7List143 triSteps18List triOuts12_18 (by decide) v7List143_lt34 =
      (ctxLinAndSteps 36 triSteps18List (by rw [triSteps18List_length]; decide)
        ⟨34, by decide⟩ ⟨35, by decide⟩ (by decide) (by decide) (by decide)
        v7List143 v7List143_lt36 v7List143_ne34 v7List143_ne35).append
      (ctxCliffAlloc (writeLinAndOuts
        (v7List143 ++ ancList 36 triSteps18List.length (by decide)) 12 54 (by decide)
        (fullAccW_lt 34 v7List143 triSteps18List.length (by decide) v7List143_lt34) triOuts12_18))
            := rfl
  rw [hs3a, tempCtx_append_assoc]
  congr 1
  exact ctxLinAndSteps_congr rfl hcat _ _ rfl rfl _ _ _ _ _ _ rfl _ _ _ _ _ _
attribute [irreducible] tailAfterTri18_143
theorem remTri18Ctx143_disj_supp (K : ℕ) (hK : K ≤ 18) : (remTri18Ctx143 K hK).DisjointFrom
    mutOrb143 ∧ (remTri18Ctx143 K hK).SupportsBelowCtx 128 := by
  have hnAcc : ∀ w ∈ v7List143 ++ ancList 36 K (by omega), ¬ mutOrb143 w := by
    intro w hw
    rcases List.mem_append.mp hw with h1 | h2
    · exact v7List143_not_mut w h1
    · have hb := (ancList_mem_bounds 36 K (by omega) w h2).1
      exact not_mutOrb143_of_ge28 (by omega)
  have hd1 := ctxLinAndSteps_disj (mutW := mutOrb143) (triSteps18List.drop K) (36 + K)
    (by rw [List.length_drop, triSteps18List_length]; omega)
    ⟨34, by decide⟩ ⟨35, by decide⟩ (by decide)
    (by dsimp; omega) (by dsimp; omega)
    (v7List143 ++ ancList 36 K (by omega))
    (accWK143_lt K hK) (accWK143_ne34 K hK) (accWK143_ne35 K hK)
    (not_mutOrb143_of_ge28 (by decide)) (not_mutOrb143_of_ge28 (by decide))
    hnAcc (fun _ hw ↦ not_mutOrb143_of_ge28 (by omega))
  have hs1 := ctxLinAndSteps_supportsBelowCtx (triSteps18List.drop K) (36 + K)
    (by rw [List.length_drop, triSteps18List_length]; omega)
    ⟨34, by decide⟩ ⟨35, by decide⟩ (by decide)
    (by dsimp; omega) (by dsimp; omega)
    (v7List143 ++ ancList 36 K (by omega))
    (accWK143_lt K hK) (accWK143_ne34 K hK) (accWK143_ne35 K hK)
  obtain ⟨hd2, hs2⟩ := tailAfterTri18_143_disj_supp
  dsimp only [remTri18Ctx143]
  exact ⟨TempCtx.disjointFrom_append hd1 hd2,
    TempCtx.supportsBelowCtx_append
      (by rw [List.length_drop, triSteps18List_length]; omega) hs1 hs2⟩
theorem remTri18Ctx143_probe (K : ℕ) (hK : K ≤ 18) :
    ∀ q : Wire 143, ScopedBlock 143 (143 - (36 + K)) (probeFwd (remTri18Ctx143 K hK))
      (.z q) ((remTri18Ctx143 K hK).plug (.z q)) := by
  have hBlock : ∀ q₀ : Wire 143,
      ∃ sRem : BitAssignment 143 → BitAssignment 143,
        ScopedBlock 143 (143 - (36 + K)) sRem (.z q₀) ((remTri18Ctx143 K hK).plug (.z q₀)) := fun
            q₀ ↦ by
    obtain ⟨sAfter, hAfter⟩ := tailAfterTri18_143_block q₀
    have heq54 : (36 + K) + (triSteps18List.drop K).length = 54 := by
      rw [List.length_drop, triSteps18List_length]; omega
    obtain ⟨sSteps, hSteps, _⟩ := ScopedBlock.ctxLinAndSteps_block
      (triSteps18List.drop K) (36 + K) (by rw [heq54]; decide)
      ⟨34, by decide⟩ ⟨35, by decide⟩ (by decide)
      (by dsimp; omega) (by dsimp; omega)
      (v7List143 ++ ancList 36 K (by omega))
      (accWK143_lt K hK) (accWK143_ne34 K hK) (accWK143_ne35 K hK)
      (.z q₀) (tailAfterTri18_143.plug (.z q₀)) sAfter (heq54.symm ▸ hAfter)
    refine ⟨fun γ ↦ sAfter (sSteps γ), ?_⟩
    dsimp only [remTri18Ctx143]
    rw [TempCtx.append_plug]
    exact hSteps
  exact scopedBlock_probeFwd (remTri18Ctx143 K hK) hBlock
/-- Unpacked-14 remaining add program (`76 - K` `TempAnd`s). -/
def remAdd14Prog143 (K : ℕ) (hK : K ≤ 18) : TempPhaseProg 143 :=
  (remTri18Ctx143 K hK).plug addOrbBody143
/-- Unpacked-14 remaining subtract program (`76 - K` `TempAnd`s). -/
def remSub14Prog143 (K : ℕ) (hK : K ≤ 18) : TempPhaseProg 143 :=
  (remTri18Ctx143 K hK).plug subOrbBody143
theorem remAdd14Prog143_full_spec (K : ℕ) (hK : K ≤ 18) : ValidCleanRem 143 (143 - (36 + K))
    (remAdd14Prog143 K hK) ∧ (remAdd14Prog143 K hK).countTempAnd = 76 - K ∧ (∀ β :
    BitAssignment 143, cleanRem 143 (143 - (36 + K)) β → (remAdd14Prog143 K hK).evalSign β =
    0) ∧ (∀ β : BitAssignment 143, cleanRem 143 (143 - (36 + K)) β → ∀ w : Wire 143,
    (remAdd14Prog143 K hK).evalBits β w = if mutOrb143 w then addOrbBody143.evalBits
    ((remTri18Ctx143 K hK).fwdBits β) w else β w) := by
  obtain ⟨hvB, hcntB, hsgnB, hnmB, _⟩ := addOrbBody143_spec
  refine orbTailProg143_full_spec_gen (remTri18Ctx143 K hK) addOrbBody143
    (remTri18Ctx143_disj_supp K hK) (by omega) (remTri18Ctx143_probe K hK) hvB hsgnB hnmB ?_
  rw [remTri18Ctx143_countTempAnd, hcntB]
  omega
theorem remSub14Prog143_full_spec (K : ℕ) (hK : K ≤ 18) : ValidCleanRem 143 (143 - (36 + K))
    (remSub14Prog143 K hK) ∧ (remSub14Prog143 K hK).countTempAnd = 76 - K ∧ (∀ β :
    BitAssignment 143, cleanRem 143 (143 - (36 + K)) β → (remSub14Prog143 K hK).evalSign β =
    0) ∧ (∀ β : BitAssignment 143, cleanRem 143 (143 - (36 + K)) β → ∀ w : Wire 143,
    (remSub14Prog143 K hK).evalBits β w = if mutOrb143 w then subOrbBody143.evalBits
    ((remTri18Ctx143 K hK).fwdBits β) w else β w) := by
  obtain ⟨hvB, hcntB, hsgnB, hnmB⟩ := subOrbBody143_spec
  refine orbTailProg143_full_spec_gen (remTri18Ctx143 K hK) subOrbBody143
    (remTri18Ctx143_disj_supp K hK) (by omega) (remTri18Ctx143_probe K hK) hvB hsgnB hnmB ?_
  rw [remTri18Ctx143_countTempAnd, hcntB]
  omega
attribute [irreducible] remAdd14Prog143 remSub14Prog143
/-- Clean-wire invariant at the `Unpacked14HeldK` hole (`36 + K` cursor + `28, 30, 32, 33, 34, 35`
  zero). -/
def Inv14Opt143 (K : ℕ) (γ : BitAssignment 143) : Prop :=
  cleanRem 143 (143 - (36 + K)) γ ∧
  γ ⟨28, by decide⟩ = 0 ∧
  γ ⟨30, by decide⟩ = 0 ∧
  γ ⟨32, by decide⟩ = 0 ∧
  γ ⟨33, by decide⟩ = 0 ∧
  γ ⟨34, by decide⟩ = 0 ∧
  γ ⟨35, by decide⟩ = 0
theorem heldTri18Ctx143_supports (K : ℕ) (hK : K ≤ 18) :
    (heldTri18Ctx143 K hK).SupportsBelowCtx (36 + K) := by
  have hlen : (triSteps18List.take K).length = K := by
    rw [List.length_take, triSteps18List_length, Nat.min_eq_left hK]
  have hs : (heldTri18Ctx143 K hK).SupportsBelowCtx (36 + (triSteps18List.take K).length) :=
    ctxLinAndSteps_supportsBelowCtx (triSteps18List.take K) 36
      (by rw [hlen]; omega)
      ⟨34, by decide⟩ ⟨35, by decide⟩ (by decide) (by decide) (by decide)
      v7List143 v7List143_lt36 v7List143_ne34 v7List143_ne35
  rwa [hlen] at hs
theorem heldTri18Ctx143_disj (K : ℕ) (hK : K ≤ 18) :
    (heldTri18Ctx143 K hK).DisjointFrom mutOrb143 :=
  ctxLinAndSteps_disj (mutW := mutOrb143) (triSteps18List.take K) 36
    (by rw [List.length_take, triSteps18List_length]; omega)
    ⟨34, by decide⟩ ⟨35, by decide⟩ (by decide) (by decide) (by decide)
    v7List143 v7List143_lt36 v7List143_ne34 v7List143_ne35
    (not_mutOrb143_of_ge28 (by decide)) (not_mutOrb143_of_ge28 (by decide))
    v7List143_not_mut (fun _ hw ↦ not_mutOrb143_of_ge28 (by omega))
theorem heldTri18Ctx143_fwd_spec (K : ℕ) (hK : K ≤ 18) :
    ValidCleanRem 143 111 ((heldTri18Ctx143 K hK).plug (.z wZero143)) ∧
    (∀ β : BitAssignment 143, cleanRem 143 111 β →
      ((heldTri18Ctx143 K hK).plug (.z wZero143)).evalBits β = β) ∧
    (∀ β : BitAssignment 143, cleanRem 143 111 β →
      β ⟨28, by decide⟩ = 0 → β ⟨30, by decide⟩ = 0 →
      Inv14Opt143 K ((heldTri18Ctx143 K hK).fwdBits β)) ∧
    (∀ (β : BitAssignment 143) (c : CanonicalTriple65),
      cleanRem 143 111 β →
      β wZero143 = 0 →
      (∀ k : Fin 12, β (wPack143 k) = packCanonVW14 c (Fin.castAdd 2 k)) →
      β wW6_143 = packCanonVW14 c ⟨12, by decide⟩ →
      β wV6_143 = packCanonVW14 c ⟨13, by decide⟩ →
      let γ := (remTri18Ctx143 K hK).fwdBits ((heldTri18Ctx143 K hK).fwdBits β)
      bitsVal (fun k : Fin 16 ↦ γ (outVW16_143 k)) + (γ (tet16W143 0)).val =
        triNum c.v.val + tetNum c.w.val) := by
  have hlen : (triSteps18List.take K).length = K := by
    rw [List.length_take, triSteps18List_length, Nat.min_eq_left hK]
  have hMain : ∀ q₀ : Wire 143,
      ValidCleanRem 143 111 ((heldTri18Ctx143 K hK).plug (.z q₀)) ∧
      (∀ β : BitAssignment 143, cleanRem 143 111 β →
        ((heldTri18Ctx143 K hK).plug (.z q₀)).evalBits β = β) ∧
      (∀ β : BitAssignment 143, cleanRem 143 111 β →
        β ⟨28, by decide⟩ = 0 → β ⟨30, by decide⟩ = 0 →
        (36 + K ≤ q₀.val → (heldTri18Ctx143 K hK).fwdBits β q₀ = 0) ∧
        (q₀.val < 36 → (heldTri18Ctx143 K hK).fwdBits β q₀ = β q₀)) := by
    intro q₀
    have hLeaf : ScopedBlock 143 (143 - (36 + (triSteps18List.take K).length)) id (.z q₀) (.z q₀) :=
      ⟨trivial, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
    obtain ⟨sSteps, hSteps0, hSpecSteps⟩ := ScopedBlock.ctxLinAndSteps_block
      (triSteps18List.take K) 36 (by rw [hlen]; omega)
      ⟨34, by decide⟩ ⟨35, by decide⟩ (by decide) (by decide) (by decide)
      v7List143 v7List143_lt36 v7List143_ne34 v7List143_ne35 (.z q₀) (.z q₀) id hLeaf
    have hBlock111 : ScopedBlock 143 111 sSteps (.z q₀) ((heldTri18Ctx143 K hK).plug (.z q₀))
        := ⟨pkValidCleanRemUp (by decide) hSteps0.valid, fun β hβ ↦ hSteps0.bits β (fun u hu ↦
        hβ u (by omega)), fun β hβ ↦ hSteps0.sign β (fun u hu ↦ hβ u (by omega))⟩
    refine ⟨hBlock111.valid, hBlock111.bits, fun β hβ h28 h30 ↦ ?_⟩
    have hSignEq : (heldTri18Ctx143 K hK).fwdBits β q₀ = sSteps β q₀ :=
      ((heldTri18Ctx143 K hK).plug_evalSign (.z q₀) β).symm.trans (hBlock111.sign β hβ)
    rw [hSignEq]
    obtain ⟨hclS, hkeepS, _⟩ := hSpecSteps β
      (fun u hu ↦ hβ u (by omega)) (hβ ⟨34, by decide⟩ (by decide)) (hβ ⟨35, by decide⟩ (by decide))
    exact ⟨fun hge ↦ hclS q₀ (by rw [hlen]; omega), fun hlt ↦ hkeepS q₀ hlt⟩
  refine ⟨(hMain wZero143).1, (hMain wZero143).2.1,
    fun β hβ h28 h30 ↦ ⟨fun w hw ↦ ((hMain w).2.2 β hβ h28 h30).1 (by omega),
      ((hMain ⟨28, by decide⟩).2.2 β hβ h28 h30).2 (by decide) ▸ h28,
      ((hMain ⟨30, by decide⟩).2.2 β hβ h28 h30).2 (by decide) ▸ h30,
      ((hMain ⟨32, by decide⟩).2.2 β hβ h28 h30).2 (by decide) ▸ hβ ⟨32, by decide⟩ (by decide),
      ((hMain ⟨33, by decide⟩).2.2 β hβ h28 h30).2 (by decide) ▸ hβ ⟨33, by decide⟩ (by decide),
      ((hMain ⟨34, by decide⟩).2.2 β hβ h28 h30).2 (by decide) ▸ hβ ⟨34, by decide⟩ (by decide),
      ((hMain ⟨35, by decide⟩).2.2 β hβ h28 h30).2 (by decide) ▸ hβ ⟨35, by decide⟩ (by decide)⟩,
    fun β c hβ hz0 hpack12 hpackW6 hpackV6 ↦ ?_⟩
  dsimp only
  rw [← PosSlots24PartnerMuxZeroT123.TempCtx.append_fwdBits, heldTri18Ctx143_append_rem]
  exact vwLutAddOpt143_fwd.2 β c hβ hz0 hpack12 hpackW6 hpackV6
/-- Probe body at cursor `36 + K` for `Unpacked14HeldK`. -/
def probeHeld14K (K : ℕ) (hK : K ≤ 18) : TempPhaseProg 143 :=
  withTempBit ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨36 + K, by omega⟩
    (by decide)
    (wire_ne_of_lt (by dsimp; omega))
    (wire_ne_of_lt (by dsimp; omega))
    (.z wZero143)
theorem probeHeld14K_valid (K : ℕ) (hK : K ≤ 18) :
    ValidCleanRem 143 (143 - (36 + K)) (probeHeld14K K hK) :=
  ⟨by dsimp; omega, trivial, fun _ _ ↦ ⟨rfl, rfl, rfl⟩⟩
theorem probeHeld14K_rem (K : ℕ) (hK : K ≤ 18) :
    ∀ rem, ValidCleanRem 143 rem (probeHeld14K K hK) → 143 - (36 + K) ≤ rem := fun rem hV ↦ by
  have hlo : 143 - rem ≤ 36 + K := hV.1
  omega
theorem probeHeld14K_bits (K : ℕ) (hK : K ≤ 18) (γ : BitAssignment 143) :
    (probeHeld14K K hK).evalBits γ = γ := by
  funext w
  dsimp only [probeHeld14K, withTempBit, TempPhaseProg.evalBits]
  by_cases hw : w = ⟨36 + K, by omega⟩
  · subst hw
    have h0a : (⟨0, by decide⟩ : Wire 143) ≠ ⟨36 + K, by omega⟩ :=
      wire_ne_of_lt (by dsimp; omega)
    have h1a : (⟨1, by decide⟩ : Wire 143) ≠ ⟨36 + K, by omega⟩ :=
      wire_ne_of_lt (by dsimp; omega)
    rw [Function.update_self, Function.update_self,
      Function.update_of_ne h0a, Function.update_of_ne h1a]
    exact CharTwo.add_cancel_right _ _
  · simp [Function.update_of_ne hw]
theorem heldTri18Ctx143_plug_probeHeld14K (K : ℕ) (hK : K ≤ 18) : ValidCleanRem 143 111
    ((heldTri18Ctx143 K hK).plug (probeHeld14K K hK)) ∧ ∀ γ : BitAssignment 143, cleanRem 143
    111 γ → ((heldTri18Ctx143 K hK).plug (probeHeld14K K hK)).evalBits γ = γ := by
  obtain ⟨hVal, hBits, _⟩ := heldTri18Ctx143_fwd_spec K hK
  have hDisjFalse := PosSlots24PartnerMuxZeroT123.tempCtx_disjointFrom_false (heldTri18Ctx143 K hK)
  have hSupp := heldTri18Ctx143_supports K hK
  refine ⟨(heldTri18Ctx143 K hK).plug_validCleanRem hDisjFalse hSupp (probeHeld14K_valid K hK)
      (fun γ w _ ↦ congrFun (probeHeld14K_bits K hK γ) w) wZero143 (by omega) hVal,
    fun γ hγ ↦ ?_⟩
  funext w
  have hsp := ((heldTri18Ctx143 K hK).plug_evalBits_split hDisjFalse
    (fun δ u _ ↦ congrFun (probeHeld14K_bits K hK δ) u) wZero143 γ).2 w not_false
  rw [hsp, hBits γ hγ]
theorem rCombTail14_143_t2 {n mClean : ℕ} (hmClean : 140 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) :
    rCombTail14_143 hmClean rOrbit16 rClean hOW wT2_143 =
      rCleanMid14 hmClean rClean ⟨1, by omega⟩ := by
  have he : (wT2_143 : Fin ((((((12 + 16) + 1) + 1) + 1) + 1) + 111)) =
      Fin.castAdd 111 (Fin.castAdd 1 (Fin.natAdd 30 (⟨0, by decide⟩ : Fin 1))) := rfl
  dsimp only [rCombTail14_143, rCleanMid14]
  rw [he, QRegister.concat_apply_left, QRegister.concat_apply_left,
      QRegister.concat_apply_right, QRegister.slice_apply, QRegister.slice_apply]
  rfl
/-- Raw `143`-wire index corresponding to `rCleanMid14[j]` (`0 ≤ j < 113`). -/
def rawIdxOf113Nat (j : ℕ) : ℕ := if j = 0 then 28 else if j = 1 then 30 else 30 + j
/-- Typed `Wire 143` index corresponding to `rCleanMid14[j]`. -/
def rawIdxOf113 (j : Fin 113) : Wire 143 :=
  ⟨rawIdxOf113Nat j.val, by dsimp [rawIdxOf113Nat]; split_ifs <;> omega⟩
theorem rCombTail14_143_rawIdxOf113 {n mClean : ℕ} (hmClean : 140 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) (j : Fin 113) :
    rCombTail14_143 hmClean rOrbit16 rClean hOW (rawIdxOf113 j) =
      rCleanMid14 hmClean rClean ⟨j.val, by omega⟩ := by
  by_cases hj0 : j.val = 0
  · have hr : rawIdxOf113 j = wZero143 := by
      ext; dsimp [rawIdxOf113, rawIdxOf113Nat]; split_ifs; rfl
    have hj' : (⟨j.val, by omega⟩ : Fin (mClean - 14)) = ⟨0, by omega⟩ := Fin.ext hj0
    rw [hr, hj', rCombTail14_143_zero]
  · by_cases hj1 : j.val = 1
    · have hr : rawIdxOf113 j = wT2_143 := by
        ext; dsimp [rawIdxOf113, rawIdxOf113Nat, wT2_143]; split_ifs; omega
      have hj' : (⟨j.val, by omega⟩ : Fin (mClean - 14)) = ⟨1, by omega⟩ := Fin.ext hj1
      rw [hr, hj', rCombTail14_143_t2]
    · let m : Fin 111 := ⟨j.val - 2, by omega⟩
      have hr : rawIdxOf113 j = ⟨32 + m.val, by omega⟩ := by
        ext; dsimp [rawIdxOf113, rawIdxOf113Nat, m]; split_ifs; omega
      have hj' : (⟨j.val, by omega⟩ : Fin (mClean - 14)) = ⟨2 + m.val, by omega⟩ := by
        ext; dsimp [m]; omega
      rw [hr, hj', rCombTail14_143_scr111 hmClean rOrbit16 rClean hOW m]
/-- `143`-wire permutation placing `triSteps18List` pebbles `[36..54)` on `rCleanMid14[0..18)`. -/
def perm143U14Nat (u : ℕ) : ℕ := if u < 28 then u else if u = 28 then 48 else if u = 29 then
    29 else if u = 30 then 49 else if u = 31 then 31 else if u = 32 then 50 else if u = 33
    then 51 else if u = 34 then 52 else if u = 35 then 53 else if u = 36 then 28 else if u =
    37 then 30 else if u < 54 then u - 6 else u
/-- Inverse `113`-wire lookup mapping `rCleanMid14[j]` back into `perm143U14Nat` domain. -/
def invPerm113U14Nat (j : ℕ) : ℕ := if j < 18 then 36 + j else if j = 18 then 28 else if j =
    19 then 30 else if j = 20 then 32 else if j = 21 then 33 else if j = 22 then 34 else if j
    = 23 then 35 else 30 + j
theorem perm143U14Nat_lt_fin : ∀ u : Fin 143, perm143U14Nat u.val < 143 := by
  decide
theorem perm143U14Nat_lt (u : ℕ) (hu : u < 143) : perm143U14Nat u < 143 :=
  perm143U14Nat_lt_fin ⟨u, hu⟩
theorem invPerm113U14Nat_lt_fin : ∀ j : Fin 113, invPerm113U14Nat j.val < 143 := by
  decide
theorem invPerm113U14Nat_lt (j : ℕ) (hj : j < 113) : invPerm113U14Nat j < 143 :=
  invPerm113U14Nat_lt_fin ⟨j, hj⟩
/-- Inverse of `perm143U14Nat` on `0 .. 142`. -/
def perm143U14InvNat (w : ℕ) : ℕ := if w < 28 then w else if w = 28 then 36 else if w = 29
    then 29 else if w = 30 then 37 else if w = 31 then 31 else if w < 48 then w + 6 else if w
    = 48 then 28 else if w = 49 then 30 else if w = 50 then 32 else if w = 51 then 33 else if
    w = 52 then 34 else if w = 53 then 35 else w
theorem perm143U14InvNat_lt_fin : ∀ w : Fin 143, perm143U14InvNat w.val < 143 := by
  decide
theorem perm143U14InvNat_lt (w : ℕ) (hw : w < 143) : perm143U14InvNat w < 143 :=
  perm143U14InvNat_lt_fin ⟨w, hw⟩
theorem invPerm113U14Nat_prop (K j : ℕ) (hK : K ≤ 18) (hj : K ≤ j) : 36 + K ≤ invPerm113U14Nat
    j ∨ invPerm113U14Nat j = 28 ∨ invPerm113U14Nat j = 30 ∨ invPerm113U14Nat j = 32 ∨
    invPerm113U14Nat j = 33 ∨ invPerm113U14Nat j = 34 ∨ invPerm113U14Nat j = 35 := by
  by_cases h18 : j = 18
  · subst h18; right; left; rfl
  · by_cases h19 : j = 19
    · subst h19; right; right; left; rfl
    · by_cases h20 : j = 20
      · subst h20; right; right; right; left; rfl
      · by_cases h21 : j = 21
        · subst h21; right; right; right; right; left; rfl
        · by_cases h22 : j = 22
          · subst h22; right; right; right; right; right; left; rfl
          · by_cases h23 : j = 23
            · subst h23; right; right; right; right; right; right; rfl
            · left; dsimp [invPerm113U14Nat]; split_ifs <;> omega
/-- Typed `Fin 143` permutation for `Unpacked14HeldK`. -/
def perm143U14Fun (u : Fin 143) : Fin 143 :=
  ⟨perm143U14Nat u.val, perm143U14Nat_lt u.val u.isLt⟩
/-- Typed `Fin 143` inverse permutation for `Unpacked14HeldK`. -/
def perm143U14InvFun (w : Fin 143) : Fin 143 :=
  ⟨perm143U14InvNat w.val, perm143U14InvNat_lt w.val w.isLt⟩
/-- Typed inverse map `Fin 113 → Fin 143` for `Unpacked14HeldK`. -/
def invPerm113U14 (j : Fin 113) : Fin 143 :=
  ⟨invPerm113U14Nat j.val, invPerm113U14Nat_lt j.val j.isLt⟩
theorem perm143U14Fun_invPerm113U14 :
    ∀ j : Fin 113, perm143U14Fun (invPerm113U14 j) = rawIdxOf113 j := by
  decide
theorem perm143U14InvFun_leftInverse :
    Function.LeftInverse perm143U14InvFun perm143U14Fun := by
  intro u; revert u; decide
theorem perm143U14Fun_injective : Function.Injective perm143U14Fun :=
  perm143U14InvFun_leftInverse.injective
theorem perm143U14Fun_mid : ∀ u : Fin 143, (u.val = 28 ∨ u.val = 30 ∨ 32 ≤ u.val) →
    (perm143U14Fun u).val = 28 ∨ (perm143U14Fun u).val = 30 ∨
    (32 ≤ (perm143U14Fun u).val ∧ (perm143U14Fun u).val < 143) := by
  decide
/-- `QRegister 143 143` permutation for `Unpacked14HeldK`. -/
def perm143U14Reg : QRegister 143 143 := ⟨⟨perm143U14Fun, perm143U14Fun_injective⟩⟩
theorem invPerm113U14_prop (K : ℕ) (hK : K ≤ 18) (j : Fin 113) (hj : K ≤ j.val) :
    36 + K ≤ (invPerm113U14 j).val ∨
    invPerm113U14 j = ⟨28, by decide⟩ ∨
    invPerm113U14 j = ⟨30, by decide⟩ ∨
    invPerm113U14 j = ⟨32, by decide⟩ ∨
    invPerm113U14 j = ⟨33, by decide⟩ ∨
    invPerm113U14 j = ⟨34, by decide⟩ ∨
    invPerm113U14 j = ⟨35, by decide⟩ := by
  rcases invPerm113U14Nat_prop K j.val hK hj with h1 | h2 | h3 | h4 | h5 | h6 | h7
  · exact Or.inl h1
  · exact Or.inr (Or.inl (Fin.ext h2))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h3)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h4))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h5)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext h6))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext h7))))))
theorem perm143U14Fun_pack12 : ∀ k : Fin 12, perm143U14Fun (wPack143 k) = wPack143 k := by
  decide
theorem perm143U14Fun_w6 : perm143U14Fun wW6_143 = wW6_143 := by decide
theorem perm143U14FunS6 : perm143U14Fun wV6_143 = wV6_143 := by decide
theorem perm143U14Fun_orb : ∀ k : Fin 16, perm143U14Fun (wOrb143 k) = wOrb143 k := by
  decide
/-- Permuted `143`-wire register for `Unpacked14HeldK` (`140 ≤ mClean`). -/
def rCombTail14_143Perm {n mClean : ℕ} (hmClean : 140 ≤ mClean) (rOrbit16 : QRegister 16 n)
    (rClean : QRegister mClean n) (hOW : rOrbit16.DisjointWires rClean) : QRegister 143 n :=
    (rCombTail14_143 hmClean rOrbit16 rClean hOW).compose perm143U14Reg
theorem rCombTail14_143Perm_apply {n mClean : ℕ} (hmClean : 140 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) (u : Wire 143) :
    rCombTail14_143Perm hmClean rOrbit16 rClean hOW u =
      rCombTail14_143 hmClean rOrbit16 rClean hOW (perm143U14Fun u) := rfl
theorem rCombTail14_143Perm_pack12 {n mClean : ℕ} (hmClean : 140 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) (k : Fin 12) : rCombTail14_143Perm hmClean rOrbit16
    rClean hOW (wPack143 k) = rHold14 hmClean rClean (Fin.castAdd 2 k) := by
  rw [rCombTail14_143Perm_apply, perm143U14Fun_pack12, rCombTail14_143_pack12]
theorem rCombTail14_143Perm_w6 {n mClean : ℕ} (hmClean : 140 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) :
    rCombTail14_143Perm hmClean rOrbit16 rClean hOW wW6_143 =
      rHold14 hmClean rClean ⟨12, by decide⟩ := by
  rw [rCombTail14_143Perm_apply, perm143U14Fun_w6, rCombTail14_143_w6]
theorem rCombTail14_143PermS6 {n mClean : ℕ} (hmClean : 140 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) :
    rCombTail14_143Perm hmClean rOrbit16 rClean hOW wV6_143 =
      rHold14 hmClean rClean ⟨13, by decide⟩ := by
  rw [rCombTail14_143Perm_apply, perm143U14FunS6, rCombTail14_143S6]
theorem rCombTail14_143Perm_orb {n mClean : ℕ} (hmClean : 140 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) (k : Fin 16) :
    rCombTail14_143Perm hmClean rOrbit16 rClean hOW (wOrb143 k) = rOrbit16 k := by
  rw [rCombTail14_143Perm_apply, perm143U14Fun_orb, rCombTail14_143_orb]
theorem rCombTail14_143Perm_invPerm113U14 {n mClean : ℕ} (hmClean : 140 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) (j : Fin 113) :
    rCombTail14_143Perm hmClean rOrbit16 rClean hOW (invPerm113U14 j) =
      rCleanMid14 hmClean rClean ⟨j.val, by omega⟩ := by
  rw [rCombTail14_143Perm_apply, perm143U14Fun_invPerm113U14, rCombTail14_143_rawIdxOf113]
/-- Explicit inverse of `rawIdxOf113` on `{28, 30} ∪ [32, 143)`. -/
def rawIdxInv143Nat (w : ℕ) : ℕ := if w = 28 then 0 else if w = 30 then 1 else if 32 ≤ w ∧ w <
    143 then w - 30 else 0
theorem rawIdxInv143Nat_lt_fin : ∀ w : Fin 143, rawIdxInv143Nat w.val < 113 := by
  decide
/-- Typed inverse map `Wire 143 → Fin 113` for `rawIdxOf113`. -/
def rawIdxInv143 (w : Wire 143) : Fin 113 := ⟨rawIdxInv143Nat w.val, rawIdxInv143Nat_lt_fin w⟩
theorem rawIdxInv143_eq : ∀ w : Wire 143, ¬ w.val < 28 → w.val ≠ 29 → w.val ≠ 31 → w =
    rawIdxOf113 (rawIdxInv143 w) := by
  decide
theorem rCombTail14_143Perm_zero_of_mid14 {n mClean : ℕ} (hmClean : 140 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) {β : BitAssignment n} (hs : SMid14 hmClean rClean β)
    (u : Wire 143) (hu : u.val = 28 ∨ u.val = 30 ∨ 32 ≤ u.val) : β
    (rCombTail14_143Perm hmClean rOrbit16 rClean hOW u) = 0 := by
  rw [rCombTail14_143Perm_apply]
  rcases perm143U14Fun_mid u hu with h28 | h30 | ⟨h32, hlt⟩
  · have heq : perm143U14Fun u = rawIdxOf113 ⟨0, by decide⟩ := Fin.ext h28
    rw [heq, rCombTail14_143_rawIdxOf113]
    exact hs ⟨0, by omega⟩
  · have heq : perm143U14Fun u = rawIdxOf113 ⟨1, by decide⟩ := Fin.ext h30
    rw [heq, rCombTail14_143_rawIdxOf113]
    exact hs ⟨1, by omega⟩
  · let j : Fin 113 := ⟨(perm143U14Fun u).val - 30, by omega⟩
    have heq : perm143U14Fun u = rawIdxOf113 j := by
      ext; dsimp [rawIdxOf113, rawIdxOf113Nat, j]; split_ifs <;> omega
    rw [heq, rCombTail14_143_rawIdxOf113]
    exact hs ⟨j.val, by omega⟩
theorem rCombTail14_143Perm_not_mem_ext {n mClean : ℕ} (hmClean : 140 ≤ mClean)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hOW : rOrbit16.DisjointWires rClean) (k : Fin (mClean - 127)) :
    rClean ⟨127 + k.val, by omega⟩ ∉
      Set.range (rCombTail14_143Perm hmClean rOrbit16 rClean hOW).wires := by
  rintro ⟨u, hu⟩
  rw [rCombTail14_143Perm_apply] at hu
  let w := perm143U14Fun u
  change rCombTail14_143 hmClean rOrbit16 rClean hOW w = _ at hu
  by_cases hw12 : w.val < 12
  · have hw_eq : w = wPack143 ⟨w.val, hw12⟩ := Fin.ext rfl
    rw [hw_eq, rCombTail14_143_pack12] at hu
    dsimp only [rHold14] at hu; rw [QRegister.slice_apply] at hu
    have hv := congrArg Fin.val (rClean.wires.injective hu); dsimp at hv; omega
  · by_cases hw28 : w.val < 28
    · have hw_eq : w = wOrb143 ⟨w.val - 12, by omega⟩ := by ext; dsimp [wOrb143]; omega
      rw [hw_eq, rCombTail14_143_orb] at hu
      exact hOW.ne _ _ hu
    · by_cases hw29 : w.val = 29
      · have hw_eq : w = wW6_143 := Fin.ext hw29
        rw [hw_eq, rCombTail14_143_w6] at hu
        dsimp only [rHold14] at hu; rw [QRegister.slice_apply] at hu
        have hv := congrArg Fin.val (rClean.wires.injective hu); dsimp at hv; omega
      · by_cases hw31 : w.val = 31
        · have hw_eq : w = wV6_143 := Fin.ext hw31
          rw [hw_eq, rCombTail14_143S6] at hu
          dsimp only [rHold14] at hu; rw [QRegister.slice_apply] at hu
          have hv := congrArg Fin.val (rClean.wires.injective hu); dsimp at hv; omega
        · let j := rawIdxInv143 w
          have hw_eq : w = rawIdxOf113 j := rawIdxInv143_eq w hw28 hw29 hw31
          rw [hw_eq, rCombTail14_143_rawIdxOf113] at hu
          dsimp only [rCleanMid14] at hu; rw [QRegister.slice_apply] at hu
          have hv := congrArg Fin.val (rClean.wires.injective hu)
          have hjlt := j.isLt; dsimp at hv; omega
theorem rCombTail14_143Perm_not_mem_core {n mClean : ℕ} (hmClean : 140 ≤ mClean)
    (rCore : QRegister posCoreWires n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCO : rCore.DisjointWires rOrbit16) (hCW : rCore.DisjointWires rClean)
    (hOW : rOrbit16.DisjointWires rClean) (i : Fin posCoreWires) :
    rCore i ∉ Set.range (rCombTail14_143Perm hmClean rOrbit16 rClean hOW).wires := by
  rintro ⟨u, hu⟩
  rw [rCombTail14_143Perm_apply] at hu
  let w := perm143U14Fun u
  change rCombTail14_143 hmClean rOrbit16 rClean hOW w = _ at hu
  by_cases hw12 : w.val < 12
  · have hw_eq : w = wPack143 ⟨w.val, hw12⟩ := Fin.ext rfl
    rw [hw_eq, rCombTail14_143_pack12] at hu
    dsimp only [rHold14] at hu; rw [QRegister.slice_apply] at hu
    exact hCW.ne i _ hu.symm
  · by_cases hw28 : w.val < 28
    · have hw_eq : w = wOrb143 ⟨w.val - 12, by omega⟩ := by ext; dsimp [wOrb143]; omega
      rw [hw_eq, rCombTail14_143_orb] at hu
      exact hCO.ne i _ hu.symm
    · by_cases hw29 : w.val = 29
      · have hw_eq : w = wW6_143 := Fin.ext hw29
        rw [hw_eq, rCombTail14_143_w6] at hu
        dsimp only [rHold14] at hu; rw [QRegister.slice_apply] at hu
        exact hCW.ne i _ hu.symm
      · by_cases hw31 : w.val = 31
        · have hw_eq : w = wV6_143 := Fin.ext hw31
          rw [hw_eq, rCombTail14_143S6] at hu
          dsimp only [rHold14] at hu; rw [QRegister.slice_apply] at hu
          exact hCW.ne i _ hu.symm
        · let j := rawIdxInv143 w
          have hw_eq : w = rawIdxOf113 j := rawIdxInv143_eq w hw28 hw29 hw31
          rw [hw_eq, rCombTail14_143_rawIdxOf113] at hu
          dsimp only [rCleanMid14] at hu; rw [QRegister.slice_apply] at hu
          exact hCW.ne i _ hu.symm
/-- Output bit map of `remAdd14Prog143` on `143` wires. -/
noncomputable def remAdd14OutBits143 (K : ℕ) (hK : K ≤ 18) (γ : BitAssignment 143) :
    BitAssignment 143 := fun w ↦ if mutOrb143 w then addOrbBody143.evalBits
    ((remTri18Ctx143 K hK).fwdBits γ) w else γ w
/-- Output bit map of `remSub14Prog143` on `143` wires. -/
noncomputable def remSub14OutBits143 (K : ℕ) (hK : K ≤ 18) (γ : BitAssignment 143) :
    BitAssignment 143 := fun w ↦ if mutOrb143 w then subOrbBody143.evalBits
    ((remTri18Ctx143 K hK).fwdBits γ) w else γ w
theorem remAdd14OutBits143_nonOrb (K : ℕ) (hK : K ≤ 18) {γ : BitAssignment 143} {w : Wire 143}
    (hw : ¬ mutOrb143 w) : remAdd14OutBits143 K hK γ w = γ w := pkIteNeg hw
theorem remSub14OutBits143_nonOrb (K : ℕ) (hK : K ≤ 18) {γ : BitAssignment 143} {w : Wire 143}
    (hw : ¬ mutOrb143 w) : remSub14OutBits143 K hK γ w = γ w := pkIteNeg hw
theorem remSub14OutBits143_remAdd14OutBits143_cancel (K : ℕ) (hK : K ≤ 18)
    {α₁ : BitAssignment 143} (hcl15 : cleanRem 143 (143 - 128) α₁) :
    remSub14OutBits143 K hK (remAdd14OutBits143 K hK α₁) = α₁ := by
  let α₂ := remAdd14OutBits143 K hK α₁
  obtain ⟨hd, hs128⟩ := remTri18Ctx143_disj_supp K hK
  have hcl₂_in : cleanRem 143 (143 - 128) α₂ := fun u hu ↦ by
    dsimp only [α₂]
    rw [remAdd14OutBits143_nonOrb K hK (not_mutOrb143_of_ge28 (by omega))]
    exact hcl15 u hu
  let γ₁ := (remTri18Ctx143 K hK).fwdBits α₁
  let γ₂ := (remTri18Ctx143 K hK).fwdBits α₂
  have hcl₁ : cleanRem 143 (143 - 128) γ₁ := fun u hu ↦ by
    dsimp only [γ₁]
    rw [TempCtx.fwdBits_outside (remTri18Ctx143 K hK) hs128 α₁ u (by omega)]
    exact hcl15 u hu
  have hcl₂ : cleanRem 143 (143 - 128) γ₂ := fun u hu ↦ by
    dsimp only [γ₂]
    rw [TempCtx.fwdBits_outside (remTri18Ctx143 K hK) hs128 α₂ u (by omega)]
    exact hcl₂_in u hu
  have hNonMutEq : ∀ w : Wire 143, ¬ mutOrb143 w → γ₂ w = γ₁ w := fun w hnm ↦
    OrbitSandHeld46.fwdBits_congr_nonMut hd (fun u hu ↦ remAdd14OutBits143_nonOrb K hK hu) w hnm
  have hOut : ∀ j : Fin 16, γ₂ (outVW16_143 j) = γ₁ (outVW16_143 j) :=
    fun j ↦ hNonMutEq _ (not_mutOrb143_of_ge28 (outVW16_143_ge28 j))
  have hCin : γ₂ (tet16W143 0) = γ₁ (tet16W143 0) :=
    hNonMutEq _ (not_mutOrb143_of_ge28 (by decide))
  have hOrb : ∀ j : Fin 16, γ₂ (wOrb143 j) = addOrbBody143.evalBits γ₁ (wOrb143 j) := fun j ↦ by
    dsimp only [γ₂]
    rw [TempCtx.fwdBits_mut hd _ ⟨j, rfl⟩]
    dsimp only [α₂, remAdd14OutBits143]
    rw [pkItePos ⟨j, rfl⟩]
  have hCancel := subOrbBody143_addOrbBody143_cancel γ₁ γ₂ hcl₁ hcl₂ hOrb hOut hCin
  funext w
  by_cases hw : mutOrb143 w
  · obtain ⟨j, rfl⟩ := hw
    dsimp only [remSub14OutBits143]
    rw [pkItePos ⟨j, rfl⟩, hCancel j]
    exact TempCtx.fwdBits_mut hd α₁ ⟨j, rfl⟩
  · rw [remSub14OutBits143_nonOrb K hK hw, remAdd14OutBits143_nonOrb K hK hw]
/-- `n`-wire step for `remAdd14Prog143`. -/
noncomputable def remAdd14Step143 {n : ℕ} (K : ℕ) (hK : K ≤ 18)
    (rComb : QRegister 143 n) (β : BitAssignment n) : BitAssignment n :=
  writeRegProg β rComb (remAdd14OutBits143 K hK (fun idx ↦ β (rComb idx)))
/-- `n`-wire step for `remSub14Prog143`. -/
noncomputable def remSub14Step143 {n : ℕ} (K : ℕ) (hK : K ≤ 18)
    (rComb : QRegister 143 n) (β : BitAssignment n) : BitAssignment n :=
  writeRegProg β rComb (remSub14OutBits143 K hK (fun idx ↦ β (rComb idx)))
theorem remAdd14Step143_apply_of_not_orb {n : ℕ} (K : ℕ) (hK : K ≤ 18)
    (rComb : QRegister 143 n) (β : BitAssignment n) {w : Wire n}
    (hw : ∀ k : Fin 16, w ≠ rComb (wOrb143 k)) : remAdd14Step143 K hK rComb β w = β w := by
  dsimp only [remAdd14Step143]
  by_cases hm : w ∈ Set.range rComb.wires
  · obtain ⟨idx, rfl⟩ := hm
    rw [writeRegProg_apply_reg]
    exact remAdd14OutBits143_nonOrb K hK fun ⟨k, hk⟩ ↦ hw k (congrArg rComb hk)
  · exact writeRegProg_apply_of_not_mem _ _ _ _ hm
theorem remSub14Step143_remAdd14Step143_cancel {n : ℕ} (K : ℕ) (hK : K ≤ 18)
    (rComb : QRegister 143 n) {β : BitAssignment n}
    (hcl15 : cleanRem 143 (143 - 128) (fun idx ↦ β (rComb idx))) :
    remSub14Step143 K hK rComb (remAdd14Step143 K hK rComb β) = β := by
  dsimp only [remSub14Step143, remAdd14Step143]
  have hread : (fun idx ↦ writeRegProg β rComb (remAdd14OutBits143 K hK (fun i ↦ β (rComb i)))
      (rComb idx)) = remAdd14OutBits143 K hK (fun i ↦ β (rComb i)) := funext fun idx ↦
      writeRegProg_apply_reg _ _ _ idx
  rw [hread, remSub14OutBits143_remAdd14OutBits143_cancel K hK hcl15]
  funext w
  by_cases hm : w ∈ Set.range rComb.wires
  · obtain ⟨idx, rfl⟩ := hm; exact writeRegProg_apply_reg _ _ _ _
  · rw [writeRegProg_apply_of_not_mem _ _ _ _ hm]
    exact writeRegProg_apply_of_not_mem _ _ _ _ hm
/-- Inner toggle-tail wrapper holding `K` `triSteps18List` pebbles across `dMid`
  (`Unpacked14HeldK`). -/
def dToggleTail14OptHeldK {Var : Type} {n mClean : ℕ} (K : ℕ) (hK : K ≤ 18)
    (hmClean : 140 ≤ mClean) (v : Var) (rOrbit16 : QRegister 16 n)
    (rClean : QRegister mClean n) (hOW : rOrbit16.DisjointWires rClean)
    (dMid : DynamicCircuit Var n) : DynamicCircuit Var n :=
  let rComb := rCombTail14_143Perm hmClean rOrbit16 rClean hOW
  let dAddRem := ((remAdd14Prog143 K hK).onRegister rComb).toDyn v
  let dSubRem := ((remSub14Prog143 K hK).onRegister rComb).toDyn v
  toDynWithDyn v rComb (.seq dAddRem (.seq dMid dSubRem)) (heldTri18Ctx143 K hK)
/-- `(1,368 - 4 * K) + dMid.count T` unpacked-`14` orbit-rank phase sandwich (`0 ≤ K ≤ 18`, `140 ≤
  mClean`),
holding `rHold14` (`14` wires) plus the first `K` `triSteps18List` pebbles across `dMid`. -/
def dOrbitSandUnpacked14OptHeldK {Var : Type} {n : ℕ} (K : ℕ) (hK : K ≤ 18) (mClean : ℕ)
    (hmClean : 140 ≤ mClean) (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean)
    (dMid : DynamicCircuit Var n) : DynamicCircuit Var n :=
  let dPk := dPack14 hmClean slot2SwappedTo0 v rCore rPartner18 rOrbit16 rClean
    hCP hCO hCW hPO hPW hOW
  let dInner := dToggleTail14OptHeldK K hK hmClean v rOrbit16 rClean hOW dMid
  .seq dPk (.seq dInner dPk)
@[simp] theorem count_dOrbitSandUnpacked14OptHeldK_toff {Var : Type} {n : ℕ} (K : ℕ)
    (hK : K ≤ 18) (mClean : ℕ) (hmClean : 140 ≤ mClean) (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean)
    (dMid : DynamicCircuit Var n) : (dOrbitSandUnpacked14OptHeldK K hK mClean hmClean
    slot2SwappedTo0 v rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW dMid).count
    TOFF = dMid.count TOFF := by
  dsimp only [dOrbitSandUnpacked14OptHeldK, dToggleTail14OptHeldK, DynamicCircuit.count]
  rw [count_dPack14_toff, toDynWithDyn_count_toff_eq]
  simp [DynamicCircuit.count, TempPhaseProg.toDyn_count_toff]
theorem count_dOrbitSandUnpacked14OptHeldK_t {Var : Type} {n : ℕ} (K : ℕ) (hK : K ≤ 18)
    (mClean : ℕ) (hmClean : 140 ≤ mClean) (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean)
    (dMid : DynamicCircuit Var n) : (dOrbitSandUnpacked14OptHeldK K hK mClean hmClean
    slot2SwappedTo0 v rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW dMid).count T =
    (1368 - 4 * K) + dMid.count T := by
  dsimp only [dOrbitSandUnpacked14OptHeldK, dToggleTail14OptHeldK, DynamicCircuit.count]
  rw [count_dPack14_t, toDynWithDyn_count_t, heldTri18Ctx143_countTempAnd]
  simp only [DynamicCircuit.count, TempPhaseProg.toDyn_count_t,
    TempPhaseProg.onRegister_countTempAnd,
    (remAdd14Prog143_full_spec K hK).2.1, (remSub14Prog143_full_spec K hK).2.1]
  omega
theorem dOrbitSandUnpacked14OptHeldK_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} (K : ℕ) (hK : K ≤ 18) (mClean : ℕ) (hmClean : 140 ≤ mClean)
    (slot2SwappedTo0 : Bool) (midPhase : Fin (2 ^ (posCoreWires + 16)) → Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean)
    (dMid : DynamicCircuit Var n) (hMid :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (rCore.concat rOrbit16 hCO)
    (rClean.slice (14 + K) (mClean - (14 + K)) (by omega)) (diagSignUnitary midPhase) dMid) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (rCore.concat rPartner18 hCP)
    (rOrbit16.concat rClean hOW) (diagSignUnitary (PosSlots24PartnerMux288.sandPhase18
    slot2SwappedTo0 midPhase)) (dOrbitSandUnpacked14OptHeldK K hK mClean hmClean
    slot2SwappedTo0 v rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW dMid) := by
  let rComb := rCombTail14_143Perm hmClean rOrbit16 rClean hOW
  let rCO := rCore.concat rOrbit16 hCO
  let rCleanMidK := rClean.slice (14 + K) (mClean - (14 + K)) (by omega)
  let P_fwd : BitAssignment 143 → Prop := fun γ ↦
    γ ⟨28, by decide⟩ = 0 ∧ γ ⟨30, by decide⟩ = 0 ∧
    γ ⟨32, by decide⟩ = 0 ∧ γ ⟨33, by decide⟩ = 0 ∧
    γ ⟨34, by decide⟩ = 0 ∧ γ ⟨35, by decide⟩ = 0
  let S_ext : BitAssignment n → Prop := fun β ↦
    ∀ k : Fin (mClean - 127), β (rClean ⟨127 + k.val, by omega⟩) = 0
  have hExtComb : ∀ (β : BitAssignment n) (f : BitAssignment 143),
      S_ext (writeRegProg β rComb f) ↔ S_ext β := fun β f ↦ by
    dsimp only [S_ext]
    refine ⟨fun h k ↦ ?_, fun h k ↦ ?_⟩
    · have hk := h k
      rwa [writeRegProg_apply_of_not_mem _ _ _ _
        (rCombTail14_143Perm_not_mem_ext hmClean rOrbit16 rClean hOW k)] at hk
    · rw [writeRegProg_apply_of_not_mem _ _ _ _
        (rCombTail14_143Perm_not_mem_ext hmClean rOrbit16 rClean hOW k)]
      exact h k
  let remHole := 143 - (36 + K)
  have hremHole : remHole ≤ 143 := by omega
  let S_hole := S_cleanCtxPred rComb P_fwd S_ext .hole remHole hremHole
  let P_hole := p2t_ketPredProj S_hole
  let dAddRem := ((remAdd14Prog143 K hK).onRegister rComb).toDyn v
  let dSubRem := ((remSub14Prog143 K hK).onRegister rComb).toDyn v
  let U_add := ((remAdd14Prog143 K hK).onRegister rComb).toToffCircuit.eval
  let U_sub := ((remSub14Prog143 K hK).onRegister rComb).toToffCircuit.eval
  have hdAdd0 : p2t_RealizesConstCleanUnitary
      (projZeroAll remHole (tailScr rComb remHole hremHole)) dAddRem U_add :=
      p2t_RealizesConstCleanUnitary_of_clean v (projZeroAll_conjTranspose remHole _)
      (PreservesStoreConst_toDyn v _) (realizes_of_validCleanRem v rComb (remAdd14Prog143 K
      hK) remHole hremHole (remAdd14Prog143_full_spec K hK).1)
  have hdSub0 : p2t_RealizesConstCleanUnitary
      (projZeroAll remHole (tailScr rComb remHole hremHole)) dSubRem U_sub :=
      p2t_RealizesConstCleanUnitary_of_clean v (projZeroAll_conjTranspose remHole _)
      (PreservesStoreConst_toDyn v _) (realizes_of_validCleanRem v rComb (remSub14Prog143 K
      hK) remHole hremHole (remSub14Prog143_full_spec K hK).1)
  have hdAddHole : p2t_RealizesConstCleanUnitary P_hole dAddRem U_add := by
    rw [p2t_projZeroAll_eq_ketPredProj] at hdAdd0
    exact p2t_RealizesConstCleanUnitary_mono_proj (p2t_ketPredProj_conjTranspose _)
      (p2t_ketPredProj_conjTranspose _) (p2t_ketPredProj_mul_imp fun _ hs ↦ hs.1) hdAdd0
  have hdSubHole : p2t_RealizesConstCleanUnitary P_hole dSubRem U_sub := by
    rw [p2t_projZeroAll_eq_ketPredProj] at hdSub0
    exact p2t_RealizesConstCleanUnitary_mono_proj (p2t_ketPredProj_conjTranspose _)
      (p2t_ketPredProj_conjTranspose _) (p2t_ketPredProj_mul_imp fun _ hs ↦ hs.1) hdSub0
  have hHoleCl : ∀ β : BitAssignment n, S_hole β →
      cleanRem 143 remHole (fun idx ↦ β (rComb idx)) := fun β hs w hw ↦ by
    have hw' : w = ⟨(143 - remHole) + (w.val - (143 - remHole)), by omega⟩ := by
      ext; dsimp; omega
    rw [hw']; exact hs.1 ⟨w.val - (143 - remHole), by omega⟩
  have hAddKet : ∀ β : BitAssignment n, S_hole β →
      U_add.1.mulVec (ket β) = ket (remAdd14Step143 K hK rComb β) := fun β hs ↦ by
    have hγCl := hHoleCl β hs
    rw [eval_onRegister_prog_ket rComb (remAdd14Prog143 K hK) β,
      (remAdd14Prog143_full_spec K hK).2.2.1 _ hγCl]
    simp only [ZMod.val_zero, _root_.pow_zero, one_smul]
    apply congrArg ket; funext w
    dsimp only [remAdd14Step143]
    have hEq : (remAdd14Prog143 K hK).evalBits (fun idx ↦ β (rComb idx)) =
        remAdd14OutBits143 K hK (fun idx ↦ β (rComb idx)) :=
      funext fun u ↦ (remAdd14Prog143_full_spec K hK).2.2.2 _ hγCl u
    rw [hEq]
  have hSubKet : ∀ β : BitAssignment n, S_hole β →
      U_sub.1.mulVec (ket β) = ket (remSub14Step143 K hK rComb β) := fun β hs ↦ by
    have hγCl := hHoleCl β hs
    rw [eval_onRegister_prog_ket rComb (remSub14Prog143 K hK) β,
      (remSub14Prog143_full_spec K hK).2.2.1 _ hγCl]
    simp only [ZMod.val_zero, _root_.pow_zero, one_smul]
    apply congrArg ket; funext w
    dsimp only [remSub14Step143]
    have hEq : (remSub14Prog143 K hK).evalBits (fun idx ↦ β (rComb idx)) =
        remSub14OutBits143 K hK (fun idx ↦ β (rComb idx)) :=
      funext fun u ↦ (remSub14Prog143_full_spec K hK).2.2.2 _ hγCl u
    rw [hEq]
  have hAddPresHole : ∀ β : BitAssignment n, S_hole β → S_hole (remAdd14Step143 K hK rComb β) :=
    fun β hs ↦ by
      have hge28 : ∀ (u : Wire 143), 28 ≤ u.val →
          remAdd14Step143 K hK rComb β (rComb u) = β (rComb u) := fun u hu ↦
        remAdd14Step143_apply_of_not_orb K hK rComb β fun k hk ↦ by
          have hv := congrArg Fin.val (rComb.wires.injective hk)
          have _ := k.isLt; dsimp [wOrb143] at hv; omega
      refine ⟨fun j ↦ ?_, ?_, (hExtComb β _).mpr hs.2.2⟩
      · dsimp only [tailScr]
        rw [hge28 _ (by dsimp [remHole]; omega)]
        exact hs.1 j
      · dsimp only [TempCtx.fwdBits, P_fwd]
        rw [hge28 ⟨28, by decide⟩ le_rfl, hge28 ⟨30, by decide⟩ (by decide),
          hge28 ⟨32, by decide⟩ (by decide), hge28 ⟨33, by decide⟩ (by decide),
          hge28 ⟨34, by decide⟩ (by decide), hge28 ⟨35, by decide⟩ (by decide)]
        exact hs.2.1
  let U_mid : Unitary (2 ^ n) := rCO.embedUnitary (diagSignUnitary midPhase)
  have hdMid0 := OrbitSandHeld46.constClean_of_embeddedCleanWorkspace
    rCO rCleanMidK (diagSignUnitary midPhase) dMid hMid
  have hdMidHole : p2t_RealizesConstCleanUnitary P_hole dMid U_mid := by
    rw [p2t_projZeroAll_eq_ketPredProj] at hdMid0
    refine p2t_RealizesConstCleanUnitary_mono_proj (p2t_ketPredProj_conjTranspose _)
      (p2t_ketPredProj_conjTranspose _) (p2t_ketPredProj_mul_imp fun β hs idx ↦ ?_) hdMid0
    dsimp only [rCleanMidK]
    rw [QRegister.slice_apply]
    by_cases hlt113 : K + idx.val < 113
    · let j : Fin 113 := ⟨K + idx.val, hlt113⟩
      have hrw : rClean ⟨(14 + K) + idx.val, by omega⟩ =
          rCleanMid14 hmClean rClean ⟨j.val, by omega⟩ := by
        dsimp only [rCleanMid14, j]; rw [QRegister.slice_apply]
        exact congrArg rClean.wires (Fin.ext (by dsimp; omega))
      rw [hrw, ← rCombTail14_143Perm_invPerm113U14 hmClean rOrbit16 rClean hOW j]
      rcases invPerm113U14_prop K hK j (by dsimp [j]; omega) with
        hge | h28 | h30 | h32 | h33 | h34 | h35
      · have hscr : rComb (invPerm113U14 j) =
            tailScr rComb remHole hremHole ⟨(invPerm113U14 j).val - (36 + K), by omega⟩ := by
          dsimp [tailScr, remHole]; congr 1; ext; dsimp; omega
        rw [hscr]; exact hs.1 _
      · rw [h28]; exact hs.2.1.1
      · rw [h30]; exact hs.2.1.2.1
      · rw [h32]; exact hs.2.1.2.2.1
      · rw [h33]; exact hs.2.1.2.2.2.1
      · rw [h34]; exact hs.2.1.2.2.2.2.1
      · rw [h35]; exact hs.2.1.2.2.2.2.2
    · have hrw : rClean ⟨(14 + K) + idx.val, by omega⟩ =
          rClean ⟨127 + ((K + idx.val) - 113), by omega⟩ :=
        congrArg rClean.wires (Fin.ext (by dsimp; omega))
      rw [hrw]
      exact hs.2.2 ⟨(K + idx.val) - 113, by omega⟩
  let phMid : BitAssignment n → ZMod 2 := fun β ↦
    if midPhase ((basisBitsEquiv (posCoreWires + 16)).symm (fun m ↦ β (rCO m))) then 1 else 0
  have hMidKet : ∀ β : BitAssignment n,
      U_mid.1.mulVec (ket β) = ((-1 : ℂ) ^ (phMid β).val) • ket β := fun β ↦
    OrbitSandHeld46.embedUnitary_diagSignUnitary_mulVec_ket_held46 rCO midPhase β
  have hCleanAdd : P_hole * (U_add.1 * P_hole) = U_add.1 * P_hole :=
    pk_ketPredProj_mul_unitary_ketPredProj U_add.1 hAddKet hAddPresHole
  have hCleanMid : P_hole * (U_mid.1 * P_hole) = U_mid.1 * P_hole :=
    pk_ketPredProj_mul_smul_ketPredProj U_mid.1 fun α _ ↦ hMidKet α
  have hdMidSub := p2t_RealizesConstCleanUnitary_seq_proj (p2t_ketPredProj_conjTranspose _)
      (p2t_ketPredProj_conjTranspose _) hdMidHole hdSubHole hCleanMid
  have hdInnerRaw := p2t_RealizesConstCleanUnitary_seq_proj (p2t_ketPredProj_conjTranspose _)
      (p2t_ketPredProj_conjTranspose _) hdAddHole hdMidSub hCleanAdd
  let phInner : BitAssignment n → ZMod 2 := fun β ↦ phMid (remAdd14Step143 K hK rComb β)
  let U₀ : Unitary (2 ^ n) := BchCubeDecoder.diagonalSignUnitaryN (fun β ↦ decide (phInner β = 1))
  have hU₀Ket : ∀ β : BitAssignment n,
      U₀.1.mulVec (ket β) = ((-1 : ℂ) ^ (phInner β).val) • ket β := fun β ↦ by
    dsimp only [U₀]; rw [BchCubeDecoder.ket_diagonalSignUnitaryN, zmod2_sign_eq]
  have hInnerEq : ((U_sub * U_mid) * U_add).1 * P_hole = U₀.1 * P_hole :=
    pk_ketPredProj_unitary_eq _ _ fun β hs ↦ by
      have hcl15 : cleanRem 143 (143 - 128) (fun idx ↦ β (rComb idx)) := fun u hu ↦
        hHoleCl β hs u (by omega)
      rw [hU₀Ket β]
      simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
      rw [hAddKet β hs, hMidKet (remAdd14Step143 K hK rComb β), Matrix.mulVec_smul,
        hSubKet (remAdd14Step143 K hK rComb β) (hAddPresHole β hs),
        remSub14Step143_remAdd14Step143_cancel K hK rComb hcl15]
  have hdInner : p2t_RealizesConstCleanUnitary P_hole (.seq dAddRem (.seq dMid dSubRem)) U₀ :=
    p2t_RealizesConstCleanUnitary_congr_unitary
      (p2t_ketPredProj_conjTranspose _) hdInnerRaw hInnerEq
  obtain ⟨hvPlug111, hPlugBits111⟩ := heldTri18Ctx143_plug_probeHeld14K K hK
  obtain ⟨U_held, hdHeldRaw, hHeldKet⟩ := p2t_realizes_toDynWithDyn_of_validPred v rComb P_fwd
      S_ext hExtComb remHole hremHole (probeHeld14K K hK) (probeHeld14K_rem K hK)
      (probeHeld14K_bits K hK) (.seq dAddRem (.seq dMid dSubRem)) U₀ hdInner phInner hU₀Ket
      (heldTri18Ctx143 K hK) 111 (by decide) hvPlug111
  let P_mid := p2t_ketPredProj (SMid14 hmClean rClean)
  have hPm_herm : P_midᴴ = P_mid := p2t_ketPredProj_conjTranspose _
  have hMidImpCl111 : ∀ β : BitAssignment n, SMid14 hmClean rClean β →
      cleanRem 143 111 (fun idx ↦ β (rComb idx)) := fun β hs u hu ↦
    rCombTail14_143Perm_zero_of_mid14 hmClean rOrbit16 rClean hOW hs u (Or.inr (Or.inr (by omega)))
  have hMidImpCtx : ∀ β : BitAssignment n, SMid14 hmClean rClean β →
      S_cleanCtxPred rComb P_fwd S_ext (heldTri18Ctx143 K hK) 111 (by decide) β := fun β hs ↦ by
    have hcl111 := hMidImpCl111 β hs
    have h28 := rCombTail14_143Perm_zero_of_mid14 hmClean rOrbit16 rClean hOW hs ⟨28, by decide⟩
        (Or.inl rfl)
    have h30 := rCombTail14_143Perm_zero_of_mid14 hmClean rOrbit16 rClean hOW hs ⟨30, by decide⟩
        (Or.inr (Or.inl rfl))
    have hInv := (heldTri18Ctx143_fwd_spec K hK).2.2.1 _ hcl111 h28 h30
    refine ⟨fun j ↦ ?_, hInv.2, fun k ↦ ?_⟩
    · dsimp only [tailScr]
      exact hcl111 ⟨(143 - 111) + j.val, by omega⟩ (by dsimp; omega)
    · have hrw : rClean ⟨127 + k.val, by omega⟩ =
          rCleanMid14 hmClean rClean ⟨113 + k.val, by omega⟩ := by
        dsimp only [rCleanMid14]; rw [QRegister.slice_apply]
        exact congrArg rClean.wires (Fin.ext (by dsimp; omega))
      rw [hrw]; exact hs _
  have hdHeld : p2t_RealizesConstCleanUnitary P_mid
      (dToggleTail14OptHeldK K hK hmClean v rOrbit16 rClean hOW dMid) U_held :=
      p2t_RealizesConstCleanUnitary_mono_proj (p2t_ketPredProj_conjTranspose _) hPm_herm
      (p2t_ketPredProj_mul_imp hMidImpCtx) hdHeldRaw
  have hHeldKetMid : ∀ β : BitAssignment n, SMid14 hmClean rClean β → U_held.1.mulVec (ket β)
      = ((-1 : ℂ) ^ (phInner (writeRegProg β rComb ((heldTri18Ctx143 K hK).fwdBits (fun idx ↦
      β (rComb idx))))).val) • ket β :=
    fun β hs ↦ by
      rw [hHeldKet β, hPlugBits111 _ (hMidImpCl111 β hs)]
      have hw : writeRegProg β rComb (fun idx ↦ β (rComb idx)) = β := by
        funext w
        by_cases hm : w ∈ Set.range rComb.wires
        · obtain ⟨idx, rfl⟩ := hm; exact writeRegProg_apply_reg _ _ _ _
        · exact writeRegProg_apply_of_not_mem _ _ _ _ hm
      rw [hw]
  let rT30 := rTarget30 hmClean rOrbit16 rClean hOW
  obtain ⟨U_pk, hdPk, hKetPk⟩ := dPack14_constClean hmClean slot2SwappedTo0 v rCore
      rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW
  have hCleanPk : P_mid * (U_pk.1 * P_mid) = U_pk.1 * P_mid :=
    pk_ketPredProj_mul_unitary_ketPredProj U_pk.1 hKetPk
      (fun _ hs ↦ packStep30_preserves_mid14 hmClean slot2SwappedTo0 rCore rPartner18 rOrbit16
          rClean hOW hs)
  have hCleanHeld : P_mid * (U_held.1 * P_mid) = U_held.1 * P_mid :=
    pk_ketPredProj_mul_smul_ketPredProj U_held.1 hHeldKetMid
  have hd23 := p2t_RealizesConstCleanUnitary_seq_proj hPm_herm hPm_herm hdHeld hdPk hCleanHeld
  have hdAllMid := p2t_RealizesConstCleanUnitary_seq_proj hPm_herm hPm_herm hdPk hd23 hCleanPk
  let rOW := rOrbit16.concat rClean hOW
  let S_ow : BitAssignment n → Prop := fun β ↦ ∀ i, β (rOW i) = 0
  have hPow_herm : (p2t_ketPredProj S_ow)ᴴ = p2t_ketPredProj S_ow :=
    p2t_ketPredProj_conjTranspose _
  have hImpOW : ∀ β : BitAssignment n, S_ow β → SMid14 hmClean rClean β := fun β hs j ↦ by
    dsimp only [rCleanMid14]; rw [QRegister.slice_apply]
    have hrw : rClean ⟨14 + j.val, by omega⟩ = rOW (Fin.natAdd 16 ⟨14 + j.val, by omega⟩) :=
      (QRegister.concat_apply_right rOrbit16 rClean hOW _).symm
    rw [hrw]; exact hs _
  have hdAllOW := p2t_RealizesConstCleanUnitary_mono_proj hPm_herm hPow_herm
    (p2t_ketPredProj_mul_imp hImpOW) hdAllMid
  let U_target : Unitary (2 ^ n) := (rCore.concat rPartner18 hCP).embedUnitary
      (diagSignUnitary (PosSlots24PartnerMux288.sandPhase18 slot2SwappedTo0 midPhase))
  have hCongr : ((U_pk * U_held) * U_pk).1 * p2t_ketPredProj S_ow =
      U_target.1 * p2t_ketPredProj S_ow :=
    pk_ketPredProj_unitary_eq _ _ fun β hs_ow ↦ by
      have hs_mid := hImpOW β hs_ow
      let β₁ := packStep30 slot2SwappedTo0 rCore rPartner18 rT30 β
      have hs₁ := packStep30_preserves_mid14 hmClean slot2SwappedTo0
        rCore rPartner18 rOrbit16 rClean hOW hs_mid
      have hCT : rCore.DisjointWires rT30 :=
        (QRegExt.disjointWires_symm
          (pk_disj_concat_left _ (QRegExt.disjointWires_symm (hCW.compose_right _))
          (QRegExt.disjointWires_symm hCO)))
      have hPT : rPartner18.DisjointWires rT30 :=
        (QRegExt.disjointWires_symm
          (pk_disj_concat_left _ (QRegExt.disjointWires_symm (hPW.compose_right _))
          (QRegExt.disjointWires_symm hPO)))
      simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
      rw [hKetPk β hs_mid, hHeldKetMid β₁ hs₁, Matrix.mulVec_smul,
        hKetPk β₁ hs₁, packStep30_invol slot2SwappedTo0 rCore rPartner18 rT30 hCT hPT β]
      have hzOrb : ∀ j : Fin 16, β (rOrbit16 j) = 0 := fun j ↦ by
        have hrw : rOrbit16 j = rOW (Fin.castAdd mClean j) :=
          (QRegister.concat_apply_left rOrbit16 rClean hOW j).symm
        rw [hrw]; exact hs_ow _
      have hzHold : ∀ k : Fin 14, β (rHold14 hmClean rClean k) = 0 := fun k ↦ by
        dsimp only [rHold14]; rw [QRegister.slice_apply]
        have hrw : rClean ⟨0 + k.val, by omega⟩ = rOW (Fin.natAdd 16 ⟨0 + k.val, by omega⟩) :=
          (QRegister.concat_apply_right rOrbit16 rClean hOW _).symm
        rw [hrw]; exact hs_ow _
      let c := canonTriple128 (rawOrbitCoord128 slot2SwappedTo0
        (fun i ↦ β (rCore i)) (fun i ↦ β (rPartner18 i)))
      have hβ₁_hold : ∀ k : Fin 14, β₁ (rHold14 hmClean rClean k) = packCanonVW14 c k := fun k ↦ by
        dsimp only [β₁]
        rw [← rTarget30_hold hmClean rOrbit16 rClean hOW k, packStep30_apply_target,
          rTarget30_hold, hzHold k, zero_add, packCanon30_hold]
      have hβ₁_orb : ∀ j : Fin 16, β₁ (rOrbit16 j) = packCanon30 c (Fin.natAdd 14 j) := fun j ↦ by
        dsimp only [β₁]
        rw [← rTarget30_orb hmClean rOrbit16 rClean hOW j, packStep30_apply_target,
          rTarget30_orb, hzOrb j, zero_add]
      let γ₀ : BitAssignment 143 := fun idx ↦ β₁ (rComb idx)
      let γ₁ : BitAssignment 143 := (heldTri18Ctx143 K hK).fwdBits γ₀
      let β_in := remAdd14Step143 K hK rComb (writeRegProg β₁ rComb γ₁)
      refine sandPhase18_ket_eq slot2SwappedTo0 midPhase rCore rPartner18 rOrbit16
        hCP hCO β β_in (fun i ↦ ?_) (fun j ↦ ?_)
      · have hnotComb := rCombTail14_143Perm_not_mem_core hmClean rCore rOrbit16 rClean hCO hCW hOW
          i
        have hnotO : ∀ k : Fin 16, rCore i ≠ rComb (wOrb143 k) :=
          fun k hk ↦ hnotComb ⟨wOrb143 k, hk.symm⟩
        dsimp only [β_in]
        rw [remAdd14Step143_apply_of_not_orb K hK rComb _ hnotO,
          writeRegProg_apply_of_not_mem _ _ _ _ hnotComb]
        exact packStep30_apply_of_not_target _ _ _ _ _ fun k ↦ hCT.ne i k
      · have hOrbEq : rOrbit16 j = rComb (wOrb143 j) :=
          (rCombTail14_143Perm_orb hmClean rOrbit16 rClean hOW j).symm
        have hread₁ : (fun idx ↦ writeRegProg β₁ rComb γ₁ (rComb idx)) = γ₁ :=
          funext fun idx ↦ writeRegProg_apply_reg _ _ _ idx
        dsimp only [β_in, remAdd14Step143]
        rw [hOrbEq, writeRegProg_apply_reg, hread₁]
        dsimp only [remAdd14OutBits143]
        rw [pkItePos ⟨j, rfl⟩]
        let γ₂ := (remTri18Ctx143 K hK).fwdBits γ₁
        have hcl111 : cleanRem 143 111 γ₀ := hMidImpCl111 β₁ hs₁
        have hz0 : γ₀ wZero143 = 0 :=
          rCombTail14_143Perm_zero_of_mid14 hmClean rOrbit16 rClean hOW hs₁ wZero143 (Or.inl rfl)
        have hpk12 : ∀ k : Fin 12, γ₀ (wPack143 k) = packCanonVW14 c (Fin.castAdd 2 k) := fun k ↦ by
          dsimp only [γ₀, rComb]; rw [rCombTail14_143Perm_pack12]; exact hβ₁_hold (Fin.castAdd 2 k)
        have hpkW6 : γ₀ wW6_143 = packCanonVW14 c ⟨12, by decide⟩ := by
          dsimp only [γ₀, rComb]; rw [rCombTail14_143Perm_w6]; exact hβ₁_hold ⟨12, by decide⟩
        have hpkV6 : γ₀ wV6_143 = packCanonVW14 c ⟨13, by decide⟩ := by
          dsimp only [γ₀, rComb]; rw [rCombTail14_143PermS6]; exact hβ₁_hold ⟨13, by decide⟩
        have hvw : bitsVal (fun k : Fin 16 ↦ γ₂ (outVW16_143 k)) + (γ₂ (tet16W143 0)).val =
            triNum c.v.val + tetNum c.w.val :=
          (heldTri18Ctx143_fwd_spec K hK).2.2.2 γ₀ c hcl111 hz0 hpk12 hpkW6 hpkV6
        have hcl15_γ₂ : cleanRem 143 (143 - 128) γ₂ := fun u hu ↦ by
          dsimp only [γ₂]
          rw [TempCtx.fwdBits_outside (remTri18Ctx143 K hK) (remTri18Ctx143_disj_supp K hK).2 γ₁ u
              (by omega)]
          dsimp only [γ₁]
          rw [TempCtx.fwdBits_outside (heldTri18Ctx143 K hK)
            (supportsBelowCtx_mono (by omega : 36 + K ≤ 128) (heldTri18Ctx143_supports K hK)) γ₀ u
                (by omega)]
          exact hcl111 u (by omega)
        have horb_fn : (fun k : Fin 16 ↦ γ₂ (wOrb143 k)) = fun k ↦ packCanon30 c (Fin.natAdd 14 k)
            := by
          funext k
          dsimp only [γ₂, γ₁, γ₀, rComb]
          rw [TempCtx.fwdBits_mut (remTri18Ctx143_disj_supp K hK).1 _ ⟨k, rfl⟩,
            TempCtx.fwdBits_mut (heldTri18Ctx143_disj K hK) _ ⟨k, rfl⟩,
            rCombTail14_143Perm_orb hmClean rOrbit16 rClean hOW k, hβ₁_orb k]
        have horb_val : bitsVal (fun k : Fin 16 ↦ γ₂ (wOrb143 k)) = c.u.val := by
          rw [horb_fn]; exact bitsVal_packCanon30_orb c
        rw [addOrbBody143_evalBits_eq_tetRank65 c hcl15_γ₂ hvw horb_val j,
          ← congrFun (basisBits_orbitRankFin16_eq slot2SwappedTo0
            (fun i ↦ β (rCore i)) (fun i ↦ β (rPartner18 i))) j]
  have hdTarget : p2t_RealizesConstCleanUnitary (rOW.basisOutcomeProjector 0)
      (dOrbitSandUnpacked14OptHeldK K hK mClean hmClean slot2SwappedTo0 v
        rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW dMid) U_target := by
    rw [p2t_basisOutcomeProjector_zero_eq_ketPredProj rOW]
    exact p2t_RealizesConstCleanUnitary_congr_unitary hPow_herm hdAllOW hCongr
  exact p2t_RealizesConstCleanUnitary_toEmbeddedCleanWorkspace
    (rCore.concat rPartner18 hCP) rOW
    (diagSignUnitary (PosSlots24PartnerMux288.sandPhase18 slot2SwappedTo0 midPhase)) _ hdTarget
attribute [irreducible] dToggleTail14OptHeldK dOrbitSandUnpacked14OptHeldK
/-- Exact base `T`-count (`+ 260 * B`) of the `13`-wire shaved packed branch (`139 ≤ mClean`). -/
def cert13Opt0BoothOptBaseT (B mClean : ℕ) : ℕ := 1376 + midK6GuardBaseT B (mClean - 13)
/-- `13`-wire shaved packed `OrbitSand` (`1,376 T` outer) wrapped around `dMidK6GuardOptDyn`. -/
noncomputable def dOrbitSandPacked13OptBoothOptDyn {Var : Type} {n mClean : ℕ} (B : ℕ)
    (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 139 ≤ mClean) (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean) :
    DynamicCircuit Var n := dOrbitSandPacked13Opt mClean hmClean slot2SwappedTo0 v rCore
    rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW (dMidK6GuardOptDyn B hB6 hB27
    (by omega) v rCore rOrbit16 (rClean.slice 13 (mClean - 13) (by omega)) hCO
    (hCW.compose_right _) (hOW.compose_right _))
theorem dOrbitSandPacked13OptBoothOptDyn_spec {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mClean : ℕ} (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 139 ≤ mClean)
    (slot2SwappedTo0 : Bool) (v : Var) (rCore : QRegister posCoreWires n)
    (rPartner18 : QRegister 18 n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean) :
    (dOrbitSandPacked13OptBoothOptDyn B hB6 hB27 hmClean slot2SwappedTo0 v rCore rPartner18
    rOrbit16 rClean hCP hCO hCW hPO hPW hOW).count TOFF = 0 ∧ (dOrbitSandPacked13OptBoothOptDyn
    B hB6 hB27 hmClean slot2SwappedTo0 v rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW
    hOW).count T ≤ cert13Opt0BoothOptBaseT B mClean + 260 * B ∧
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (rCore.concat rPartner18 hCP)
    (rOrbit16.concat rClean hOW) (diagSignUnitary (PosSlots24PartnerMux288.sandPhase18
    slot2SwappedTo0 (midPhaseBitSpec slot2SwappedTo0 pos24TailSign (pos24TailMag30MidpointB B
    (by omega) (by omega))))) (dOrbitSandPacked13OptBoothOptDyn B hB6 hB27 hmClean
    slot2SwappedTo0 v rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW) := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [dOrbitSandPacked13OptBoothOptDyn]
    rw [count_dOrbitSandPacked13Opt_toff, count_dMidK6GuardOptDyn_toff]
  · dsimp only [dOrbitSandPacked13OptBoothOptDyn, cert13Opt0BoothOptBaseT]
    rw [count_dOrbitSandPacked13Opt_t]
    have hMid := count_dMidK6GuardOptDyn_t_le_exact B hB6 hB27 (by omega) v
      rCore rOrbit16 (rClean.slice 13 (mClean - 13) (by omega))
      hCO (hCW.compose_right _) (hOW.compose_right _)
    omega
  · dsimp only [dOrbitSandPacked13OptBoothOptDyn]
    rw [← sandPhase18_k6MidPhaseBitSpecB_eq B (by omega) (by omega) slot2SwappedTo0]
    exact dOrbitSandPacked13Opt_realizes mClean hmClean slot2SwappedTo0 _ v rCore
      rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW _ (dMidK6GuardOptDyn_realizes B hB6
      hB27 (by omega) slot2SwappedTo0 v rCore rOrbit16 (rClean.slice 13 (mClean - 13)
      (by omega)) hCO (hCW.compose_right _) (hOW.compose_right _))
theorem count_dOrbitSandPacked13OptBoothOptDyn_toff {Var : Type} {n mClean : ℕ} (B : ℕ)
    (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 139 ≤ mClean) (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean) :
    (dOrbitSandPacked13OptBoothOptDyn B hB6 hB27 hmClean slot2SwappedTo0 v rCore rPartner18
    rOrbit16 rClean hCP hCO hCW hPO hPW hOW).count TOFF = 0 := by
  dsimp only [dOrbitSandPacked13OptBoothOptDyn]
  rw [count_dOrbitSandPacked13Opt_toff, count_dMidK6GuardOptDyn_toff]
theorem count_dOrbitSandPacked13OptBoothOptDyn_t_le {Var : Type} {n mClean : ℕ} (B : ℕ)
    (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 139 ≤ mClean) (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean) :
    (dOrbitSandPacked13OptBoothOptDyn B hB6 hB27 hmClean slot2SwappedTo0 v rCore rPartner18
    rOrbit16 rClean hCP hCO hCW hPO hPW hOW).count T ≤ cert13Opt0BoothOptBaseT B mClean + 260 *
    B := by
  dsimp only [dOrbitSandPacked13OptBoothOptDyn, cert13Opt0BoothOptBaseT]
  rw [count_dOrbitSandPacked13Opt_t]
  have hMid := count_dMidK6GuardOptDyn_t_le_exact B hB6 hB27 (by omega) v
    rCore rOrbit16 (rClean.slice 13 (mClean - 13) (by omega))
    hCO (hCW.compose_right _) (hOW.compose_right _)
  omega
attribute [irreducible] dOrbitSandPacked13OptBoothOptDyn
/-- Exact base `T`-count (`+ 260 * B`) of `(14 + K)`-wire shaved `Unpacked14HeldK` (`K ≤ 18`, `140
  + K ≤ mClean`). -/
def cert14BoothOptBaseT (B mClean K : ℕ) : ℕ :=
  (1368 - 4 * K) + midK6GuardBaseT B (mClean - (14 + K))
/-- `(14 + K)`-wire shaved `Unpacked14HeldK` (`(1,368 - 4 * K) T` outer) wrapped around
  `dMidK6GuardOptDyn`. -/
noncomputable def dOrbitSandUnpacked14HeldKGuardDyn {Var : Type} {n mClean : ℕ} (K : ℕ)
    (hK : K ≤ 18) (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 140 + K ≤ mClean)
    (slot2SwappedTo0 : Bool) (v : Var) (rCore : QRegister posCoreWires n)
    (rPartner18 : QRegister 18 n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean) :
    DynamicCircuit Var n := dOrbitSandUnpacked14OptHeldK K hK mClean (by omega)
    slot2SwappedTo0 v rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW
    (dMidK6GuardOptDyn B hB6 hB27 (by omega) v rCore rOrbit16 (rClean.slice (14 + K) (mClean
    - (14 + K)) (by omega)) hCO (hCW.compose_right _) (hOW.compose_right _))
theorem dOrbitSandUnpacked14HeldKGuardDyn_spec {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mClean : ℕ} (K : ℕ) (hK : K ≤ 18) (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27)
    (hmClean : 140 + K ≤ mClean) (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean) :
    (dOrbitSandUnpacked14HeldKGuardDyn K hK B hB6 hB27 hmClean slot2SwappedTo0 v rCore
    rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW).count TOFF = 0 ∧
    (dOrbitSandUnpacked14HeldKGuardDyn K hK B hB6 hB27 hmClean slot2SwappedTo0 v rCore
    rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW).count T ≤ cert14BoothOptBaseT B mClean K
    + 260 * B ∧ DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
    (rCore.concat rPartner18 hCP) (rOrbit16.concat rClean hOW) (diagSignUnitary
    (PosSlots24PartnerMux288.sandPhase18 slot2SwappedTo0 (midPhaseBitSpec slot2SwappedTo0
    pos24TailSign (pos24TailMag30MidpointB B (by omega) (by omega)))))
    (dOrbitSandUnpacked14HeldKGuardDyn K hK B hB6 hB27 hmClean slot2SwappedTo0 v rCore
    rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW) := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [dOrbitSandUnpacked14HeldKGuardDyn]
    rw [count_dOrbitSandUnpacked14OptHeldK_toff, count_dMidK6GuardOptDyn_toff]
  · dsimp only [dOrbitSandUnpacked14HeldKGuardDyn, cert14BoothOptBaseT]
    rw [count_dOrbitSandUnpacked14OptHeldK_t]
    have hMid := count_dMidK6GuardOptDyn_t_le_exact B hB6 hB27 (by omega) v
      rCore rOrbit16 (rClean.slice (14 + K) (mClean - (14 + K)) (by omega))
      hCO (hCW.compose_right _) (hOW.compose_right _)
    omega
  · dsimp only [dOrbitSandUnpacked14HeldKGuardDyn]
    rw [← sandPhase18_k6MidPhaseBitSpecB_eq B (by omega) (by omega) slot2SwappedTo0]
    exact dOrbitSandUnpacked14OptHeldK_realizes K hK mClean (by omega) slot2SwappedTo0 _ v
      rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW _ (dMidK6GuardOptDyn_realizes
      B hB6 hB27 (by omega) slot2SwappedTo0 v rCore rOrbit16 (rClean.slice (14 + K) (mClean -
      (14 + K)) (by omega)) hCO (hCW.compose_right _) (hOW.compose_right _))
/-- Running minimum of `cert14BoothOptBaseT B mClean K` over `0 ≤ K ≤ m`. -/
def best14From (B mClean : ℕ) : ℕ → ℕ
  | 0 => cert14BoothOptBaseT B mClean 0
  | m + 1 => min (best14From B mClean m) (cert14BoothOptBaseT B mClean (m + 1))
/-- Dynamic circuit realizing `best14From B mClean m` across `K ∈ [0..m]` (`m ≤ 18`, `140 + m ≤
  mClean`). -/
noncomputable def dBest14From {Var : Type} {n mClean : ℕ}
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27)
    (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean) :
    (m : ℕ) → m ≤ 18 → 140 + m ≤ mClean → DynamicCircuit Var n
  | 0, _, hCl =>
      dOrbitSandUnpacked14HeldKGuardDyn 0 (by decide) B hB6 hB27 hCl slot2SwappedTo0 v
        rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW
  | m + 1, hm, hCl =>
      if best14From B mClean m ≤ cert14BoothOptBaseT B mClean (m + 1) then
        dBest14From B hB6 hB27 slot2SwappedTo0 v
          rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW m (by omega) (by omega)
      else
        dOrbitSandUnpacked14HeldKGuardDyn (m + 1) hm B hB6 hB27 hCl slot2SwappedTo0 v
          rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW
theorem dBest14From_toff {Var : Type} {n mClean : ℕ}
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27)
    (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean) :
    ∀ (m : ℕ) (hm : m ≤ 18) (hCl : 140 + m ≤ mClean),
      (dBest14From B hB6 hB27 slot2SwappedTo0 v
        rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW m hm hCl).count TOFF = 0
  | 0, _, hCl => by
      dsimp only [dBest14From, dOrbitSandUnpacked14HeldKGuardDyn]
      rw [count_dOrbitSandUnpacked14OptHeldK_toff, count_dMidK6GuardOptDyn_toff]
  | m + 1, hm, hCl => by
      dsimp only [dBest14From]
      split_ifs
      · exact dBest14From_toff B hB6 hB27 slot2SwappedTo0 v
          rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW m (by omega) (by omega)
      · dsimp only [dOrbitSandUnpacked14HeldKGuardDyn]
        rw [count_dOrbitSandUnpacked14OptHeldK_toff, count_dMidK6GuardOptDyn_toff]
theorem dBest14From_t_le {Var : Type} {n mClean : ℕ}
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27)
    (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean) :
    ∀ (m : ℕ) (hm : m ≤ 18) (hCl : 140 + m ≤ mClean),
      (dBest14From B hB6 hB27 slot2SwappedTo0 v
        rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW m hm hCl).count T ≤
        best14From B mClean m + 260 * B
  | 0, _, hCl => by
      dsimp only [dBest14From, best14From, dOrbitSandUnpacked14HeldKGuardDyn, cert14BoothOptBaseT]
      rw [count_dOrbitSandUnpacked14OptHeldK_t]
      have hMid := count_dMidK6GuardOptDyn_t_le_exact B hB6 hB27 (by omega) v
        rCore rOrbit16 (rClean.slice (14 + 0) (mClean - (14 + 0)) (by omega))
        hCO (hCW.compose_right _) (hOW.compose_right _)
      omega
  | m + 1, hm, hCl => by
      dsimp only [dBest14From, best14From]
      split_ifs with hle
      · have ih := dBest14From_t_le B hB6 hB27 slot2SwappedTo0 v
          rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW m (by omega) (by omega)
        omega
      · have hCertAux : (dOrbitSandUnpacked14HeldKGuardDyn (m + 1) hm B hB6 hB27 hCl slot2SwappedTo0
          v
            rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW).count T ≤
            cert14BoothOptBaseT B mClean (m + 1) + 260 * B := by
          dsimp only [dOrbitSandUnpacked14HeldKGuardDyn, cert14BoothOptBaseT]
          rw [count_dOrbitSandUnpacked14OptHeldK_t]
          have hMid := count_dMidK6GuardOptDyn_t_le_exact B hB6 hB27 (by omega) v
            rCore rOrbit16 (rClean.slice (14 + (m + 1)) (mClean - (14 + (m + 1))) (by omega))
            hCO (hCW.compose_right _) (hOW.compose_right _)
          omega
        omega
theorem dBest14From_realizes {Var : Type} [Fintype Var] [DecidableEq Var] {n mClean : ℕ}
    (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27)
    (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean) :
    ∀ (m : ℕ) (hm : m ≤ 18) (hCl : 140 + m ≤ mClean),
      DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace
        (rCore.concat rPartner18 hCP) (rOrbit16.concat rClean hOW)
        (diagSignUnitary
          (PosSlots24PartnerMux288.sandPhase18 slot2SwappedTo0
            (midPhaseBitSpec slot2SwappedTo0 pos24TailSign
              (pos24TailMag30MidpointB B (by omega) (by omega)))))
        (dBest14From B hB6 hB27 slot2SwappedTo0 v
          rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW m hm hCl)
  | 0, _, hCl =>
      (dOrbitSandUnpacked14HeldKGuardDyn_spec 0 (by decide) B hB6 hB27 hCl slot2SwappedTo0 v
        rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW).2.2
  | m + 1, hm, hCl => by
      dsimp only [dBest14From]
      split_ifs
      · exact dBest14From_realizes B hB6 hB27 slot2SwappedTo0 v
          rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW m (by omega) (by omega)
      · exact (dOrbitSandUnpacked14HeldKGuardDyn_spec (m + 1) hm B hB6 hB27 hCl slot2SwappedTo0 v
          rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW).2.2
attribute [irreducible] dOrbitSandUnpacked14HeldKGuardDyn dBest14From
/-- Exact base `T`-count (`+ 260 * B`) of `dOrbitSandAnchorBoothOptDyn` across `138 ≤ mClean` and `6
  ≤ B ≤ 27`,
taking the minimum across `Packed12Opt` (`138+`), `Packed13Opt` (`139+`), `Unpacked14HeldK` (`K ∈
[0..18]`, `140+`),
and `orbitSandAnchorGuardBaseT` (`Packed13HeldK` + `Packed18HeldK`). -/
def orbitSandAnchorBoothOptBaseT (B mClean : ℕ) : ℕ :=
  let c0 := cert12BoothOptBaseT B mClean
  let c1 := if 139 ≤ mClean then min c0 (cert13Opt0BoothOptBaseT B mClean) else c0
  if 140 ≤ mClean then min c1 (best14From B mClean (min 18 (mClean - 140))) else c1
/-- Master Slim-Cone `138 ≤ mClean` Stage-B orbit-rank phase sandwich (`0` `TOFF`), drop-in
  compatible
with `dOrbitSandAnchorGuardDyn` and `dOrbitSandAnchorMasterOptDyn`. -/
noncomputable def dOrbitSandAnchorBoothOptDyn {Var : Type} {n mClean : ℕ} (B : ℕ) (hB6 : 6 ≤ B)
    (hB27 : B ≤ 27) (hmClean : 138 ≤ mClean) (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean) :
    DynamicCircuit Var n :=
  let d12 := dOrbitSandPacked12BoothOptDyn B hB6 hB27 hmClean slot2SwappedTo0 v
    rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW
  let c0 := cert12BoothOptBaseT B mClean
  let d0 : DynamicCircuit Var n := d12
  let c1 := if 139 ≤ mClean then min c0 (cert13Opt0BoothOptBaseT B mClean) else c0
  let d1 : DynamicCircuit Var n := if h139 : 139 ≤ mClean then if c0 ≤ cert13Opt0BoothOptBaseT B
      mClean then d0 else dOrbitSandPacked13OptBoothOptDyn B hB6 hB27 h139 slot2SwappedTo0 v
      rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW else d0
  if h140 : 140 ≤ mClean then
    if c1 ≤ best14From B mClean (min 18 (mClean - 140)) then d1
    else dBest14From B hB6 hB27 slot2SwappedTo0 v
      rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW
      (min 18 (mClean - 140)) (Nat.min_le_left _ _) (by omega)
  else d1
@[simp] theorem count_dOrbitSandAnchorBoothOptDyn_toff {Var : Type} {n mClean : ℕ} (B : ℕ)
    (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 138 ≤ mClean) (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean) :
    (dOrbitSandAnchorBoothOptDyn B hB6 hB27 hmClean slot2SwappedTo0 v rCore rPartner18 rOrbit16
    rClean hCP hCO hCW hPO hPW hOW).count TOFF = 0 := by
  have hd12 := count_dOrbitSandPacked12BoothOptDyn_toff B hB6 hB27 hmClean slot2SwappedTo0 v
    rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW
  dsimp only [dOrbitSandAnchorBoothOptDyn]
  split_ifs <;> first
    | exact hd12
    | exact count_dOrbitSandPacked13OptBoothOptDyn_toff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    | exact dBest14From_toff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
theorem count_dOrbitSandAnchorBoothOptDyn_t_le_exact {Var : Type} {n mClean : ℕ} (B : ℕ)
    (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 138 ≤ mClean) (slot2SwappedTo0 : Bool) (v : Var)
    (rCore : QRegister posCoreWires n) (rPartner18 : QRegister 18 n)
    (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean) :
    (dOrbitSandAnchorBoothOptDyn B hB6 hB27 hmClean slot2SwappedTo0 v rCore rPartner18 rOrbit16
    rClean hCP hCO hCW hPO hPW hOW).count T ≤ orbitSandAnchorBoothOptBaseT B mClean + 260 * B
    := by
  have hd12 := count_dOrbitSandPacked12BoothOptDyn_t_le B hB6 hB27 hmClean slot2SwappedTo0 v
    rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW
  dsimp only [dOrbitSandAnchorBoothOptDyn, orbitSandAnchorBoothOptBaseT]
  by_cases h139 : 139 ≤ mClean
  · have hd13 := count_dOrbitSandPacked13OptBoothOptDyn_t_le B hB6 hB27 h139 slot2SwappedTo0 v
      rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW
    by_cases h140 : 140 ≤ mClean
    · have hd14 := dBest14From_t_le B hB6 hB27 slot2SwappedTo0 v
        rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW
        (min 18 (mClean - 140)) (Nat.min_le_left _ _) (by omega)
      simp only [h139, h140, ↓reduceDIte, ↓reduceIte]
      split_ifs <;> omega
    · simp only [h139, h140, ↓reduceDIte, ↓reduceIte]
      split_ifs <;> omega
  · have hn140 : ¬ (140 ≤ mClean) := by omega
    simp only [h139, hn140, ↓reduceDIte, ↓reduceIte]
    omega
theorem dOrbitSandAnchorBoothOptDyn_realizes {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mClean : ℕ} (B : ℕ) (hB6 : 6 ≤ B) (hB27 : B ≤ 27) (hmClean : 138 ≤ mClean)
    (slot2SwappedTo0 : Bool) (v : Var) (rCore : QRegister posCoreWires n)
    (rPartner18 : QRegister 18 n) (rOrbit16 : QRegister 16 n) (rClean : QRegister mClean n)
    (hCP : rCore.DisjointWires rPartner18) (hCO : rCore.DisjointWires rOrbit16)
    (hCW : rCore.DisjointWires rClean) (hPO : rPartner18.DisjointWires rOrbit16)
    (hPW : rPartner18.DisjointWires rClean) (hOW : rOrbit16.DisjointWires rClean) :
    DynCircuitExt.RealizesEmbeddedUnitaryWithCleanWorkspace (rCore.concat rPartner18 hCP)
    (rOrbit16.concat rClean hOW) (diagSignUnitary (PosSlots24PartnerMux288.sandPhase18
    slot2SwappedTo0 (midPhaseBitSpec slot2SwappedTo0 pos24TailSign (pos24TailMag30MidpointB B
    (by omega) (by omega))))) (dOrbitSandAnchorBoothOptDyn B hB6 hB27 hmClean slot2SwappedTo0 v
    rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW) := by
  have hd12 := (dOrbitSandPacked12BoothOptDyn_spec B hB6 hB27 hmClean slot2SwappedTo0 v
    rCore rPartner18 rOrbit16 rClean hCP hCO hCW hPO hPW hOW).2.2
  dsimp only [dOrbitSandAnchorBoothOptDyn]
  split_ifs <;> first
    | exact hd12
    | exact (dOrbitSandPacked13OptBoothOptDyn_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).2.2
    | exact dBest14From_realizes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
attribute [irreducible] dOrbitSandAnchorBoothOptDyn
/-- Stage-B `T`-count under the `25,734 T` fast `64 × 4` outer wrapper. -/
def stageBFastBoothOptAnchorT (B mClean : ℕ) : ℕ :=
  25734 + orbitSandAnchorBoothOptBaseT B mClean + 260 * B
end Part1_OrbitSandBoothOpt
section Part2_ShiftedPartnerFastBoothOpt
set_option maxRecDepth 16384
local instance (priority := 1000000) instNeZeroTwoPowBoothOptP2 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open PrimitiveGate (TOFF T)
open MeasureBranchHadamardSem (ket bitSign sqrtHalf bit_cases
  eval_seq_mulVec ket_H ket_X ket_CNOT ket_TOFF matrix_ext_ket ket_projector_zero
  ket_projector_one)
open CoinDispatchedBarrel288 (coinBarrelIdxFast)
open CoinDispatchedBarrel288.Internal (CliffProg)
open FullSysCatSegmentBridge (disjointWires_concat_left)
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open PosSlots24PartnerMuxZeroT123 hiding ite_pos ite_neg dite_pos dite_neg
/-- `CliffProg M` predicate certifying all target wires have index `≥ base`. -/
def CliffWritesAbove {M : ℕ} (base : ℕ) : CliffProg M → Prop
  | .nil => True
  | .x q => base ≤ q.val
  | .cnot _ t _ => base ≤ t.val
  | .seq c₁ c₂ => CliffWritesAbove base c₁ ∧ CliffWritesAbove base c₂
theorem CliffWritesAbove.inv {M : ℕ} {base : ℕ} :
    ∀ {c : CliffProg M}, CliffWritesAbove base c → CliffWritesAbove base c.inv
  | .nil, _ => trivial
  | .x _, h => h
  | .cnot _ _ _, h => h
  | .seq _ _, ⟨h₁, h₂⟩ => ⟨h₂.inv, h₁.inv⟩
theorem CliffWritesAbove.eval_lt {M : ℕ} {base : ℕ} :
    ∀ {c : CliffProg M}, CliffWritesAbove base c →
      ∀ (γ : BitAssignment M) (idx : Wire M), idx.val < base → c.eval γ idx = γ idx
  | .nil, _, _, _, _ => rfl
  | .x q, hq, γ, idx, hlt => by
      have hne : idx ≠ q := wire_ne_of_lt (lt_of_lt_of_le hlt hq)
      exact Function.update_of_ne hne _ _
  | .cnot ctrl tgt _, ht, γ, idx, hlt => by
      have hne : idx ≠ tgt := wire_ne_of_lt (lt_of_lt_of_le hlt ht)
      exact Function.update_of_ne hne _ _
  | .seq c₁ c₂, ⟨h₁, h₂⟩, γ, idx, hlt =>
      (h₂.eval_lt (c₁.eval γ) idx hlt).trans (h₁.eval_lt γ idx hlt)
/-- `6 + 2` binary radix decomposition of an `8`-bit value (`v = v % 64 + 64 * (v / 64)`). -/
theorem bitsVal_split_6_2 (b : Fin 8 → ZMod 2) :
    bitsVal b =
      bitsVal (fun j : Fin 6 ↦ b ⟨j.val, by omega⟩) +
      64 * bitsVal (fun j : Fin 2 ↦ b ⟨6 + j.val, by omega⟩) := by
  simp only [bitsVal, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ]
  change (b 0).val * 1 + ((b 1).val * 2 + ((b 2).val * 4 + ((b 3).val * 8 + ((b 4).val * 16 +
    ((b 5).val * 32 + ((b 6).val * 64 + ((b 7).val * 128 + 0))))))) = ((b 0).val * 1 + ((b
    1).val * 2 + ((b 2).val * 4 + ((b 3).val * 8 + ((b 4).val * 16 + ((b 5).val * 32 + 0))))))
    + 64 * ((b 6).val * 1 + ((b 7).val * 2 + 0))
  ring
theorem cliffWritesAbove_comm_embedUnitary {M n kAct : ℕ}
    (rAct : QRegister kAct n) (V : Unitary (2 ^ kAct))
    (rComb : QRegister M n) (base : ℕ)
    (hOutNotAct : ∀ idx : Wire M, base ≤ idx.val → rComb idx ∉ Set.range rAct.wires)
    (hCombPres : ∀ (idx : Wire M) (g : Fin (2 ^ n)) (y : Fin (2 ^ kAct)),
      V.1 y (rAct.extractIndex g) ≠ 0 →
      basisBits n (rAct.replaceIndex g y) (rComb idx) = basisBits n g (rComb idx)) :
    ∀ {c : CliffProg M}, CliffWritesAbove base c →
      (c.onRegister rComb).toCircuit.eval * rAct.embedUnitary V =
        rAct.embedUnitary V * (c.onRegister rComb).toCircuit.eval
  | .nil, _ => by
      change 1 * rAct.embedUnitary V = rAct.embedUnitary V * 1
      rw [one_mul, mul_one]
  | .x q, hq =>
      comm_embedUnitary_of_update_outside rAct V
        (Circuit.X (rComb q)) (rComb q) (hOutNotAct q hq)
        (fun _ ↦ 1)
        (fun β ↦ ket_X (rComb q) β)
        (fun _ _ _ ↦ rfl)
  | .cnot ctrl tgt hne, ht =>
      comm_embedUnitary_of_update_outside rAct V
        (Circuit.CNOT (rComb ctrl) (rComb tgt) (rComb.wires.injective.ne hne))
        (rComb tgt) (hOutNotAct tgt ht)
        (fun β ↦ β (rComb ctrl))
        (fun β ↦ ket_CNOT (rComb ctrl) (rComb tgt) (rComb.wires.injective.ne hne) β)
        (fun g y hnz ↦ hCombPres ctrl g y hnz)
  | .seq c₁ c₂, ⟨h₁, h₂⟩ => by
      have ih₁ := cliffWritesAbove_comm_embedUnitary rAct V rComb base hOutNotAct hCombPres h₁
      have ih₂ := cliffWritesAbove_comm_embedUnitary rAct V rComb base hOutNotAct hCombPres h₂
      change ((c₂.onRegister rComb).toCircuit.eval * (c₁.onRegister rComb).toCircuit.eval) *
        rAct.embedUnitary V = rAct.embedUnitary V * ((c₂.onRegister rComb).toCircuit.eval *
        (c₁.onRegister rComb).toCircuit.eval)
      calc
        ((c₂.onRegister rComb).toCircuit.eval * (c₁.onRegister rComb).toCircuit.eval) *
            rAct.embedUnitary V
          = (c₂.onRegister rComb).toCircuit.eval *
              ((c₁.onRegister rComb).toCircuit.eval * rAct.embedUnitary V) := mul_assoc _ _ _
        _ = ((c₂.onRegister rComb).toCircuit.eval * rAct.embedUnitary V) *
              (c₁.onRegister rComb).toCircuit.eval := by rw [ih₁, ← mul_assoc]
        _ = rAct.embedUnitary V *
              ((c₂.onRegister rComb).toCircuit.eval * (c₁.onRegister rComb).toCircuit.eval) := by
              rw [ih₂, mul_assoc]
/-! ## Section 2B: `DiagCtxWG` & Coherent Zero-Gated `Pow2` W-State Router -/
/-- Decidable pairwise disjointness predicate on `Wire M` for a coherent zero-gated
`Pow2` W-state router. -/
def DisjWCohGate1 {D N M : ℕ} (wHas : Wire M) (wIdx : Fin D → Wire M) (wOut : Fin N → Wire M)
    (qEnc : Wire M) : Prop := (∀ j, wHas ≠ wOut j) ∧ wHas ≠ qEnc ∧ (∀ d j, wIdx d ≠ wOut j) ∧
    (∀ d, wIdx d ≠ qEnc) ∧ Function.Injective wOut ∧ (∀ j, wOut j ≠ qEnc)
theorem wRouterDisj_onRegister {D N M n : ℕ} (rComb : QRegister M n) {wHas : Wire M}
    {wIdx : Fin D → Wire M} {wOut : Fin N → Wire M} {qEnc : Wire M}
    (hd : DisjWCohGate1 wHas wIdx wOut qEnc) : WRouterDisj (rComb wHas)
    (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l)) (rComb qEnc) := ⟨fun j ↦
    rComb.wires.injective.ne (hd.1 j), rComb.wires.injective.ne hd.2.1, fun d j ↦
    rComb.wires.injective.ne (hd.2.2.1 d j), fun d ↦ rComb.wires.injective.ne (hd.2.2.2.1 d),
    fun _ _ hij ↦ rComb.wires.injective.ne (hd.2.2.2.2.1.ne hij), fun j ↦
    rComb.wires.injective.ne (hd.2.2.2.2.2 j)⟩
theorem wInj_w1Of {D n : ℕ} {wOut : Fin (2 ^ D) → Wire n}
    (hInj : ∀ i j, i ≠ j → wOut i ≠ wOut j) :
    WInj (fun (_ : Fin 1) p ↦ wOut p) := fun b₁ p₁ b₂ p₂ heq ↦
  ⟨Subsingleton.elim b₁ b₂, Decidable.byContradiction fun hne ↦ hInj p₁ p₂ hne heq⟩
/-- Pre-measurement circuit for coherent zero-gated W-shift round `d < D` (`2 T`, `0` Toffoli). -/
def cCohShiftPre {D n : ℕ} (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin (2 ^ D) → Wire n) (qEnc : Wire n)
    (hHasQ : wHas ≠ qEnc) (hIdxQ : ∀ d, wIdx d ≠ qEnc) (hOutQ : ∀ p, wOut p ≠ qEnc)
    (d : ℕ) (hd : d < D) : Circuit n :=
  cnotOddToEnc 1 D (fun _ p ↦ wOut p) qEnc (fun _ p ↦ hOutQ p) d ;;ᶜ
  Circuit.X wHas ;;ᶜ
  chGateCirc wHas qEnc hHasQ ;;ᶜ
  Circuit.X wHas ;;ᶜ
  Circuit.CNOT (wIdx ⟨d, hd⟩) qEnc (hIdxQ ⟨d, hd⟩)
theorem count_cCohShiftPre {D n : ℕ} (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin (2 ^ D) → Wire n) (qEnc : Wire n) (hHasQ : wHas ≠ qEnc)
    (hIdxQ : ∀ d, wIdx d ≠ qEnc) (hOutQ : ∀ p, wOut p ≠ qEnc) (d : ℕ) (hd : d < D) :
    (cCohShiftPre wHas wIdx wOut qEnc hHasQ hIdxQ hOutQ d hd).count T = 2 ∧
    (cCohShiftPre wHas wIdx wOut qEnc hHasQ hIdxQ hOutQ d hd).count TOFF = 0 := by
  obtain ⟨to_, fo_⟩ := count_cnotOddToEnc 1 D (fun _ p ↦ wOut p) qEnc (fun _ p ↦ hOutQ p) d
  obtain ⟨tc, fc⟩ := count_chGateCirc wHas qEnc hHasQ
  refine ⟨?_, ?_⟩ <;>
    simp [cCohShiftPre, Circuit.count_seq, Circuit.X, Circuit.CNOT, to_, fo_, tc, fc]
/-- Level `d < D` coherent zero-gated Z-measurement shift step (`2 T`, `0` Toffoli). -/
def wCohShiftLevel {Var : Type} {D n : ℕ} (v : Var) (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin (2 ^ D) → Wire n) (qEnc : Wire n) (hHasQ : wHas ≠ qEnc)
    (hIdxQ : ∀ d, wIdx d ≠ qEnc) (hOutInj : ∀ i j, i ≠ j → wOut i ≠ wOut j)
    (hOutQ : ∀ p, wOut p ≠ qEnc) (d : ℕ) (hd : d < D) : DynamicCircuit Var n := .seq
    (.circuit (cCohShiftPre wHas wIdx wOut qEnc hHasQ hIdxQ hOutQ d hd)) (zResetFixupDyn v
    qEnc (barrelSwap 1 D (fun _ p ↦ wOut p) (wInj_w1Of hOutInj) d))
/-- First `m ≤ D` levels of `wCohShiftLevel` (`2 * m` `T`, `0` Toffoli). -/
def wCohShiftLevels {Var : Type} {D n : ℕ} (v : Var) (wHas : Wire n)
    (wIdx : Fin D → Wire n) (wOut : Fin (2 ^ D) → Wire n) (qEnc : Wire n)
    (hHasQ : wHas ≠ qEnc) (hIdxQ : ∀ d, wIdx d ≠ qEnc)
    (hOutInj : ∀ i j, i ≠ j → wOut i ≠ wOut j) (hOutQ : ∀ p, wOut p ≠ qEnc) :
    (m : ℕ) → m ≤ D → DynamicCircuit Var n
  | 0, _ => .circuit .identity
  | d + 1, hd =>
      .seq (wCohShiftLevels v wHas wIdx wOut qEnc hHasQ hIdxQ hOutInj hOutQ d
        (Nat.le_of_succ_le hd))
        (wCohShiftLevel v wHas wIdx wOut qEnc hHasQ hIdxQ hOutInj hOutQ d hd)
theorem count_wCohShiftLevels {Var : Type} {D n : ℕ} (v : Var) (wHas : Wire n)
    (wIdx : Fin D → Wire n) (wOut : Fin (2 ^ D) → Wire n) (qEnc : Wire n)
    (hHasQ : wHas ≠ qEnc) (hIdxQ : ∀ d, wIdx d ≠ qEnc)
    (hOutInj : ∀ i j, i ≠ j → wOut i ≠ wOut j) (hOutQ : ∀ p, wOut p ≠ qEnc) :
    ∀ (m : ℕ) (hm : m ≤ D),
      (wCohShiftLevels v wHas wIdx wOut qEnc hHasQ hIdxQ hOutInj hOutQ m hm).count T = 2 * m ∧
      (wCohShiftLevels v wHas wIdx wOut qEnc hHasQ hIdxQ hOutInj hOutQ m hm).count TOFF = 0
  | 0, _ => ⟨rfl, rfl⟩
  | d + 1, hd => by
      obtain ⟨t0, f0⟩ := count_wCohShiftLevels v wHas wIdx wOut qEnc hHasQ hIdxQ hOutInj hOutQ d
        (Nat.le_of_succ_le hd)
      obtain ⟨tp, fp⟩ := count_cCohShiftPre wHas wIdx wOut qEnc hHasQ hIdxQ hOutQ d hd
      obtain ⟨tb, fb⟩ := count_barrelSwap 1 D (fun _ p ↦ wOut p) (wInj_w1Of hOutInj) d
      dsimp only [wCohShiftLevels, wCohShiftLevel, DynamicCircuit.count]
      rw [t0, f0, tp, fp, count_zResetFixupDyn_t, count_zResetFixupDyn_toff, tb, fb]
      exact ⟨by omega, rfl⟩
open Classical in
/-- Forward coherent zero-gated `Pow2` W-state one-hot router
(`2 * (2 ^ (k + 1) + k)` `T`, `0` Toffoli). -/
noncomputable def wStateComputeCohGate1 (k : ℕ) {Var : Type} {n : ℕ} (v : Var)
    (wHas : Wire n) (wIdx : Fin (k + 1) → Wire n) (wOut : Fin (2 ^ (k + 1)) → Wire n)
    (qEnc : Wire n) : DynamicCircuit Var n :=
  if h : WRouterDisjProp wHas wIdx wOut qEnc then
    let hw := wInj_w1Of h.2.2.2.2.1
    .seq
      (.circuit (Circuit.CNOT wHas (wOut ⟨0, Nat.two_pow_pos (k + 1)⟩) (h.1 _) ;;ᶜ
        wTreePrefix 1 (k + 1) (fun _ p ↦ wOut p) hw (k + 1) le_rfl))
      (wCohShiftLevels v wHas wIdx wOut qEnc h.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2 (k + 1) le_rfl)
  else
    .circuit (seqNat (2 * (2 ^ (k + 1) + k)) fun _ _ ↦ Circuit.T wHas)
open Classical in
/-- MBU uncomputation for coherent zero-gated `Pow2` W-state one-hot router (`0 T`, `0` Toffoli). -/
noncomputable def wStateUncomputeCohGate1 (k : ℕ) {Var : Type} {n : ℕ} (v : Var)
    (wHas : Wire n) (wIdx : Fin (k + 1) → Wire n) (wOut : Fin (2 ^ (k + 1)) → Wire n) :
    DynamicCircuit Var n := if h : WRouterOutDisj wHas wIdx wOut then wUncompTreeDyn v 1
    (k + 1) wIdx (fun _ p ↦ wOut p) (wInj_w1Of h.2.2) (fun d _ p ↦ h.2.1 d p) (.circuit
    (Circuit.CNOT wHas (wOut ⟨0, Nat.two_pow_pos (k + 1)⟩) (h.1 _))) (k + 1) le_rfl else
    .circuit .identity
theorem count_wStateComputeCohGate1 (k : ℕ) {Var : Type} {n : ℕ} (v : Var) (wHas : Wire n)
    (wIdx : Fin (k + 1) → Wire n) (wOut : Fin (2 ^ (k + 1)) → Wire n) (qEnc : Wire n) :
    (wStateComputeCohGate1 k v wHas wIdx wOut qEnc).count T = 2 * (2 ^ (k + 1) + k) ∧
    (wStateComputeCohGate1 k v wHas wIdx wOut qEnc).count TOFF = 0 := by
  dsimp only [wStateComputeCohGate1]
  by_cases h : WRouterDisjProp wHas wIdx wOut qEnc
  · rw [dite_eq_left h]
    obtain ⟨tt, tf⟩ := count_wTreePrefix 1 (k + 1) (fun _ p ↦ wOut p)
      (wInj_w1Of h.2.2.2.2.1) (k + 1) le_rfl
    obtain ⟨st, sf⟩ := count_wCohShiftLevels v wHas wIdx wOut qEnc
      h.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2 (k + 1) le_rfl
    dsimp only [DynamicCircuit.count]
    rw [Circuit.count_seq, Circuit.count_seq, tt, tf, st, sf]
    have hcT : (Circuit.CNOT wHas (wOut ⟨0, Nat.two_pow_pos (k + 1)⟩) (h.1 _)).count T = 0 := by
      simp [Circuit.CNOT]
    have hcF : (Circuit.CNOT wHas (wOut ⟨0, Nat.two_pow_pos (k + 1)⟩) (h.1 _)).count TOFF = 0 := by
      simp [Circuit.CNOT]
    rw [hcT, hcF]
    have hp : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    exact ⟨by omega, rfl⟩
  · rw [dite_eq_right h]
    dsimp only [DynamicCircuit.count]
    have ht := count_seqNat_T 1 (2 * (2 ^ (k + 1) + k))
      (fun _ _ ↦ Circuit.T wHas) (fun _ _ ↦ by simp [Circuit.T])
    have hf := count_seqNat_TOFF_zero (2 * (2 ^ (k + 1) + k))
      (fun _ _ ↦ Circuit.T wHas) (fun _ _ ↦ by simp [Circuit.T])
    exact ⟨ht.trans (Nat.mul_one _), hf⟩
theorem count_wStateUncomputeCohGate1 (k : ℕ) {Var : Type} {n : ℕ} (v : Var)
    (wHas : Wire n) (wIdx : Fin (k + 1) → Wire n) (wOut : Fin (2 ^ (k + 1)) → Wire n) :
    (wStateUncomputeCohGate1 k v wHas wIdx wOut).count T = 0 ∧
    (wStateUncomputeCohGate1 k v wHas wIdx wOut).count TOFF = 0 := by
  dsimp only [wStateUncomputeCohGate1]
  by_cases h : WRouterOutDisj wHas wIdx wOut
  · rw [dite_eq_left h]
    obtain ⟨ut, uf⟩ := count_wUncompTreeDyn_opt v 1 (k + 1) wIdx (fun _ p ↦ wOut p)
        (wInj_w1Of h.2.2) (fun d _ p ↦ h.2.1 d p) (.circuit (Circuit.CNOT wHas (wOut ⟨0,
        Nat.two_pow_pos (k + 1)⟩) (h.1 _))) (k + 1) le_rfl
    rw [ut, uf]
    constructor <;> simp [DynamicCircuit.count, Circuit.CNOT]
  · rw [dite_eq_right h]
    exact ⟨rfl, rfl⟩
/-- Subspace precondition for `wStateComputeCohGate1` (no restriction on `wIdx` when `wHas = 0`). -/
def ValidWCohGateIn {N n : ℕ} (wOut : Fin N → Wire n) (qEnc : Wire n) (δ : BitAssignment n) :
    Prop := (∀ j : Fin N, δ (wOut j) = 0) ∧ δ qEnc = 0
/-- Subspace precondition on clean output state for `wStateUncomputeCohGate1`. -/
def ValidWCohGateClean {N n : ℕ} (wOut : Fin N → Wire n) (δ : BitAssignment n) : Prop :=
  ∀ j : Fin N, δ (wOut j) = 0
/-- Intermediate state vector at coherent shift level `d ≤ D`
(`wSuperVec` on `wHas = 1`, `ket δ` on `wHas = 0`). -/
noncomputable def wCohSuperVec {D n : ℕ} (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin (2 ^ D) → Wire n) (qEnc : Wire n) (δ : BitAssignment n) (d : ℕ) (hd : d ≤ D) :
    Fin (2 ^ n) → ℂ := if (∀ p : Fin (2 ^ D), δ (wOut p) = 0) ∧ δ qEnc = 0 then if δ wHas = 1
    then wSuperVec (fun _ ↦ (0 : Fin 1)) wIdx (fun _ p ↦ wOut p) qEnc δ d hd else ket δ else 0
/-- Operator mapping computational basis kets via `wCohSuperVec`. -/
noncomputable def wCohSuperOp {D n : ℕ} (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin (2 ^ D) → Wire n) (qEnc : Wire n) (d : ℕ) (hd : d ≤ D) : Operator (2 ^ n) :=
    mkVecOp fun δ ↦ wCohSuperVec wHas wIdx wOut qEnc δ d hd
theorem x_chGate_x_mulVec_ket_of_one {n : ℕ} {wHas qEnc : Wire n} (hHasQ : wHas ≠ qEnc)
    {β : BitAssignment n} (h1 : β wHas = 1) :
    (Circuit.X wHas ;;ᶜ chGateCirc wHas qEnc hHasQ ;;ᶜ Circuit.X wHas).eval.1.mulVec (ket β) =
      ket β := by
  simp only [eval_seq_mulVec]
  rw [ket_X, h1, show (1 : ZMod 2) + 1 = 0 from rfl,
    chGateCirc_mulVec_ket_zero wHas qEnc hHasQ _ (Function.update_self _ _ _),
    ket_X, Function.update_idem, Function.update_self, zero_add,
    show (1 : ZMod 2) = β wHas from h1.symm, Function.update_eq_self]
theorem x_chGate_x_mulVec_ket_of_zero {n : ℕ} {wHas qEnc : Wire n} (hHasQ : wHas ≠ qEnc)
    {δ : BitAssignment n} (h0 : δ wHas = 0) (hq0 : δ qEnc = 0) :
    (Circuit.X wHas ;;ᶜ chGateCirc wHas qEnc hHasQ ;;ᶜ Circuit.X wHas).eval.1.mulVec (ket δ) =
      sqrtHalf • (ket δ + ket (Function.update δ qEnc 1)) := by
  let δ₁ := Function.update δ wHas 1
  have hq1 : δ₁ qEnc = 0 := (Function.update_of_ne hHasQ.symm 1 δ).trans hq0
  simp only [eval_seq_mulVec]
  rw [ket_X, h0, zero_add,
    show Function.update δ wHas 1 = δ₁ from rfl,
    chGateCirc_mulVec_ket_one wHas qEnc hHasQ δ₁ (Function.update_self _ _ _),
    ket_H qEnc δ₁, hq1, show bitSign (0 : ZMod 2) = (1 : ℂ) from rfl, one_smul,
    update_eq_self_of_zero hq1, Matrix.mulVec_smul, Matrix.mulVec_add]
  congr 1; congr 1
  · dsimp only [δ₁]
    rw [ket_X, Function.update_idem, Function.update_self,
      CharTwo.add_self_eq_zero, update_eq_self_of_zero h0]
  · dsimp only [δ₁]
    rw [Function.update_comm hHasQ, ket_X, Function.update_idem, Function.update_self,
      CharTwo.add_self_eq_zero,
      update_eq_self_of_zero ((Function.update_of_ne hHasQ 1 δ).trans h0)]
theorem cCohShiftPre_mulVec_ket_act {D n : ℕ} (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin (2 ^ D) → Wire n) (qEnc : Wire n)
    (hd : WRouterDisj wHas wIdx wOut qEnc) (d : ℕ) (hdLt : d < D)
    (δ : BitAssignment n) (hHas1 : δ wHas = 1)
    (hw0 : ∀ p, δ (wOut p) = 0) (hq0 : δ qEnc = 0)
    {hi : ℕ} (hhi : hi < 2 ^ (D - d)) :
    let lo := idxValPrefix wIdx δ d (Nat.le_of_lt hdLt)
    let pS : Fin (2 ^ D) := ⟨lo + 2 ^ d * hi,
      shift_pos_lt (Nat.le_of_lt hdLt) (idxValPrefix_lt_two_pow wIdx δ d (Nat.le_of_lt hdLt)) hhi⟩
    (cCohShiftPre wHas wIdx wOut qEnc hd.has_ne_q hd.idx_ne_q hd.out_ne_q d hdLt).eval.1.mulVec
        (ket (Function.update δ (wOut pS) 1)) =
      ket (Function.update (Function.update δ (wOut pS) 1) qEnc
        ((if decide (hi % 2 = 1) then (1 : ZMod 2) else 0) + δ (wIdx ⟨d, hdLt⟩))) := by
  intro lo pS
  let w : Fin 1 → Fin (2 ^ D) → Wire n := fun _ p ↦ wOut p
  have hw : WInj w := wInj_w1Of hd.out_inj
  have h1 :
      (cCohShiftPre wHas wIdx wOut qEnc hd.has_ne_q hd.idx_ne_q hd.out_ne_q d hdLt).eval.1.mulVec
        (ket (Function.update δ (w 0 pS) 1)) =
      (cnotOddToEnc 1 D w qEnc (fun _ p ↦ hd.out_ne_q p) d ;;ᶜ
        Circuit.CNOT (wIdx ⟨d, hdLt⟩) qEnc (hd.idx_ne_q ⟨d, hdLt⟩)).eval.1.mulVec
      (ket (Function.update δ (w 0 pS) 1)) := by
    dsimp only [cCohShiftPre]
    simp only [eval_seq_mulVec]
    rw [cnotOddToEnc_mulVec_ket w qEnc hw (fun _ p ↦ hd.out_ne_q p) d δ (fun _ p ↦ hw0 p) hq0 0 pS]
    let β₁ := Function.update (Function.update δ (w 0 pS) 1) qEnc
      (if pS.val.testBit d then 1 else 0)
    have hβ₁Has : β₁ wHas = 1 := by
      dsimp only [β₁, w]
      rw [Function.update_of_ne hd.has_ne_q, Function.update_of_ne (hd.has_ne_out pS), hHas1]
    have hX := x_chGate_x_mulVec_ket_of_one hd.has_ne_q hβ₁Has
    simp only [eval_seq_mulVec] at hX
    change (Circuit.CNOT (wIdx ⟨d, hdLt⟩) qEnc (hd.idx_ne_q ⟨d, hdLt⟩)).eval.1.mulVec
      ((Circuit.X wHas).eval.1.mulVec ((chGateCirc wHas qEnc hd.has_ne_q).eval.1.mulVec
      ((Circuit.X wHas).eval.1.mulVec (ket β₁)))) = (Circuit.CNOT (wIdx ⟨d, hdLt⟩) qEnc
      (hd.idx_ne_q ⟨d, hdLt⟩)).eval.1.mulVec (ket β₁)
    rw [hX]
  exact h1.trans (cnotOddAndIdx_mulVec_ket wIdx w qEnc hw (fun _ p ↦ hd.out_ne_q p)
    hd.idx_ne_q (fun d' _ p ↦ hd.idx_ne_out d' p) d hdLt δ (fun _ p ↦ hw0 p) hq0 0 hhi)
theorem cCohShiftPre_mulVec_ket_inact {D n : ℕ} (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin (2 ^ D) → Wire n) (qEnc : Wire n) (hd : WRouterDisj wHas wIdx wOut qEnc)
    (d : ℕ) (hdLt : d < D) (δ : BitAssignment n) (hHas0 : δ wHas = 0)
    (hw0 : ∀ p, δ (wOut p) = 0) (hq0 : δ qEnc = 0) : (cCohShiftPre wHas wIdx wOut qEnc
    hd.has_ne_q hd.idx_ne_q hd.out_ne_q d hdLt).eval.1.mulVec (ket δ) = sqrtHalf •
    (ket δ + ket (Function.update δ qEnc 1)) := by
  dsimp only [cCohShiftPre]
  simp only [eval_seq_mulVec]
  rw [cnotOddToEnc_mulVec_ket_zero (fun (_ : Fin 1) p ↦ wOut p) qEnc
    (fun _ p ↦ hd.out_ne_q p) d δ (fun _ p ↦ hw0 p)]
  have hX := x_chGate_x_mulVec_ket_of_zero hd.has_ne_q hHas0 hq0
  simp only [eval_seq_mulVec] at hX
  rw [hX, Matrix.mulVec_smul, Matrix.mulVec_add]
  congr 1
  rcases bit_cases (δ (wIdx ⟨d, hdLt⟩)) with hu0 | hu1
  · rw [ket_CNOT_ctrl_zero _ hu0,
      ket_CNOT_ctrl_zero _ ((Function.update_of_ne (hd.idx_ne_q ⟨d, hdLt⟩) 1 δ).trans hu0)]
  · rw [ket_CNOT, hq0, hu1, zero_add,
      ket_CNOT, Function.update_self, Function.update_of_ne (hd.idx_ne_q ⟨d, hdLt⟩), hu1,
      CharTwo.add_self_eq_zero, Function.update_idem, update_eq_self_of_zero hq0, add_comm]
theorem subspaceStep_wCohShiftLevel {Var : Type} [Fintype Var] [DecidableEq Var] {D n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (wHas : Wire n) (wIdx : Fin D → Wire n)
    (wOut : Fin (2 ^ D) → Wire n) (qEnc : Wire n) (hd : WRouterDisj wHas wIdx wOut qEnc)
    (d : ℕ) (hdLt : d < D) : SubspaceStep
    (wCohSuperOp wHas wIdx wOut qEnc d (Nat.le_of_lt hdLt))
    (wCohSuperOp wHas wIdx wOut qEnc (d + 1) hdLt) (wCohShiftLevel v wHas wIdx wOut qEnc
    hd.has_ne_q hd.idx_ne_q hd.out_inj hd.out_ne_q d hdLt) := by
  let w : Fin 1 → Fin (2 ^ D) → Wire n := fun _ p ↦ wOut p
  have hw : WInj w := wInj_w1Of hd.out_inj
  let cPre := cCohShiftPre wHas wIdx wOut qEnc hd.has_ne_q hd.idx_ne_q hd.out_ne_q d hdLt
  let cB := barrelSwap 1 D w hw d
  have hev (q : Fin (2 ^ (D - (d + 1)))) : ¬ decide (2 * q.val % 2 = 1) = true := by
    simp only [decide_eq_true_eq]; omega
  have hod (q : Fin (2 ^ (D - (d + 1)))) : decide ((2 * q.val + 1) % 2 = 1) = true := by
    simp only [decide_eq_true_eq]; omega
  have hEv (q : Fin (2 ^ (D - (d + 1)))) : 2 * q.val < 2 ^ (D - d) := by
    have h : 2 ^ (D - d) = 2 * 2 ^ (D - (d + 1)) := by
      rw [show D - d = D - (d + 1) + 1 by omega, Nat.pow_succ]; ring
    have := q.isLt; omega
  have hOd (q : Fin (2 ^ (D - (d + 1)))) : 2 * q.val + 1 < 2 ^ (D - d) := by
    have h : 2 ^ (D - d) = 2 * 2 ^ (D - (d + 1)) := by
      rw [show D - d = D - (d + 1) + 1 by omega, Nat.pow_succ]; ring
    have := q.isLt; omega
  have stepSplit (F : Operator (2 ^ n))
      (hActSum : ∀ (δ : BitAssignment n) (_hHas1 : δ wHas = 1)
        (_hw0 : ∀ p, δ (wOut p) = 0) (_hq0 : δ qEnc = 0),
        let lo := idxValPrefix wIdx δ d (Nat.le_of_lt hdLt)
        let hlo : lo < 2 ^ d := idxValPrefix_lt_two_pow wIdx δ d (Nat.le_of_lt hdLt)
        let kIn (hi : ℕ) (hhi : hi < 2 ^ (D - d)) := ket (Function.update δ (wOut ⟨lo + 2 ^ d
            * hi, shift_pos_lt (Nat.le_of_lt hdLt) hlo hhi⟩) 1)
        let kOut (q : Fin (2 ^ (D - (d + 1)))) := ket (Function.update δ (wOut
          ⟨idxValPrefix wIdx δ (d + 1) hdLt + 2 ^ (d + 1) * q.val,
            shift_pos_lt hdLt (idxValPrefix_lt_two_pow wIdx δ (d + 1) hdLt) q.isLt⟩) 1)
        (∑ q : Fin (2 ^ (D - (d + 1))), F.mulVec (cPre.eval.1.mulVec (kIn (2 * q.val) (hEv q)))) +
          (∑ q : Fin (2 ^ (D - (d + 1))),
            F.mulVec (cPre.eval.1.mulVec (kIn (2 * q.val + 1) (hOd q)))) =
          ∑ q : Fin (2 ^ (D - (d + 1))), kOut q)
      (hInact : ∀ (δ : BitAssignment n), δ wHas = 0 → (∀ p, δ (wOut p) = 0) → δ qEnc = 0 →
        F.mulVec (cPre.eval.1.mulVec (ket δ)) = sqrtHalf • ket δ) :
      F * (cPre.eval.1 * wCohSuperOp wHas wIdx wOut qEnc d (Nat.le_of_lt hdLt)) =
        sqrtHalf • wCohSuperOp wHas wIdx wOut qEnc (d + 1) hdLt := by
    apply matrix_ext_ket; intro δ
    simp only [← Matrix.mulVec_mulVec, Matrix.smul_mulVec,
      wCohSuperOp, mkVecOp_mulVec_ket, wCohSuperVec]
    by_cases hV : (∀ p : Fin (2 ^ D), δ (wOut p) = 0) ∧ δ qEnc = 0
    · have ⟨hw0, hq0⟩ := hV
      rw [ite_eq_left hV, ite_eq_left hV]
      rcases bit_cases (δ wHas) with hHas0 | hHas1
      · have hne1 : ¬ (δ wHas = 1) := by rw [hHas0]; decide
        rw [ite_eq_right hne1, ite_eq_right hne1]
        exact hInact δ hHas0 hw0 hq0
      · rw [ite_eq_left hHas1, ite_eq_left hHas1]
        dsimp only [wSuperVec]
        have hV' : (∀ (b : Fin 1) (p : Fin (2 ^ D)), δ (wOut p) = 0) ∧ δ qEnc = 0 :=
          ⟨fun _ p ↦ hw0 p, hq0⟩
        rw [ite_eq_left hV', ite_eq_left hV',
          Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_sum, Matrix.mulVec_sum]
        have hkd : D - d = D - (d + 1) + 1 := by omega
        have hpow : sqrtHalf ^ (D - d) = sqrtHalf * sqrtHalf ^ (D - (d + 1)) := by
          rw [hkd, _root_.pow_succ']
        rw [hpow, smul_smul]; congr 1
        let e : Fin (2 ^ (D - (d + 1))) ⊕ Fin (2 ^ (D - (d + 1))) ≃ Fin (2 ^ (D - d)) :=
          (finTwoMulEquiv (2 ^ (D - (d + 1)))).trans (finCongr (by rw [hkd, Nat.pow_succ]; ring))
        rw [← e.sum_comp, Fintype.sum_sum_type]
        exact hActSum δ hHas1 hw0 hq0
    · rw [ite_eq_right hV, ite_eq_right hV, Matrix.mulVec_zero, Matrix.mulVec_zero, smul_zero]
  refine subspaceStep_seq_zResetFixup v qEnc cB
    (subspaceStep_of_circuit (Var := Var)
      (wCohSuperOp wHas wIdx wOut qEnc d (Nat.le_of_lt hdLt)) cPre)
    (stepSplit ((QRegister.singleton qEnc).basisOutcomeProjector 0) ?_ ?_)
    (stepSplit (cB.eval.1 * (Circuit.X qEnc).eval.1 *
      (QRegister.singleton qEnc).basisOutcomeProjector 1) ?_ ?_)
  · intro δ hHas1 hw0 hq0 lo hlo kIn kOut
    let P₀ := (QRegister.singleton qEnc).basisOutcomeProjector 0
    have hPre {hi : ℕ} (hhi : hi < 2 ^ (D - d)) :=
      cCohShiftPre_mulVec_ket_act wHas wIdx wOut qEnc hd d hdLt δ hHas1 hw0 hq0 hhi
    have hqId (p : Fin (2 ^ D)) :
        Function.update (Function.update δ (wOut p) 1) qEnc 0 = Function.update δ (wOut p) 1 :=
      update_eq_self_of_zero ((Function.update_of_ne (hd.out_ne_q p).symm 1 δ).trans hq0)
    have ketEq {a b : ℕ} {ha : a < 2 ^ D} {hb : b < 2 ^ D} (h : a = b) :
        ket (Function.update δ (wOut ⟨a, ha⟩) 1) = ket (Function.update δ (wOut ⟨b, hb⟩) 1) :=
      congrArg (fun p ↦ ket (Function.update δ (wOut p) 1)) (Fin.ext h)
    rcases bit_cases (δ (wIdx ⟨d, hdLt⟩)) with hu0 | hu1
    · have hs1 : (∑ q, P₀.mulVec (cPre.eval.1.mulVec (kIn (2 * q.val) (hEv q)))) = ∑ q, kOut q :=
        Finset.sum_congr rfl fun q _ ↦ by
          dsimp only [P₀, cPre, kIn, kOut]
          rw [hPre (hEv q), ite_eq_right (hev q), hu0, add_zero,
            ket_projector_zero, Function.update_self, ite_eq_left rfl, hqId]
          exact ketEq (by dsimp [idxValPrefix, lo]; rw [ite_eq_right (by rw [hu0]; decide)]; ring)
      have hs0 : (∑ q, P₀.mulVec (cPre.eval.1.mulVec (kIn (2 * q.val + 1) (hOd q)))) = 0 :=
        Finset.sum_eq_zero fun q _ ↦ by
          dsimp only [P₀, cPre, kIn]
          rw [hPre (hOd q), ite_eq_left (hod q), hu0, add_zero,
            ket_projector_zero, Function.update_self, ite_eq_right one_ne_zero]
      rw [hs1, hs0, add_zero]
    · have hs0 : (∑ q, P₀.mulVec (cPre.eval.1.mulVec (kIn (2 * q.val) (hEv q)))) = 0 :=
        Finset.sum_eq_zero fun q _ ↦ by
          dsimp only [P₀, cPre, kIn]
          rw [hPre (hEv q), ite_eq_right (hev q), hu1, zero_add,
            ket_projector_zero, Function.update_self, ite_eq_right one_ne_zero]
      have hs1 : (∑ q, P₀.mulVec (cPre.eval.1.mulVec (kIn (2 * q.val + 1) (hOd q)))) =
          ∑ q, kOut q :=
        Finset.sum_congr rfl fun q _ ↦ by
          dsimp only [P₀, cPre, kIn, kOut]
          rw [hPre (hOd q), ite_eq_left (hod q), hu1, CharTwo.add_self_eq_zero,
            ket_projector_zero, Function.update_self, ite_eq_left rfl, hqId]
          exact ketEq (by dsimp [idxValPrefix, lo]; rw [ite_eq_left hu1]; ring)
      rw [hs0, hs1, zero_add]
  · intro δ hHas0 hw0 hq0
    dsimp only [cPre]
    rw[cCohShiftPre_mulVec_ket_inact wHas wIdx wOut qEnc hd d hdLt δ hHas0 hw0 hq0,
        Matrix.mulVec_smul, Matrix.mulVec_add, ket_projector_zero, ite_eq_left hq0,
        ket_projector_zero, Function.update_self, ite_eq_right one_ne_zero, add_zero]
  · intro δ hHas1 hw0 hq0 lo hlo kIn kOut
    let F₁ := cB.eval.1 * (Circuit.X qEnc).eval.1 *
      (QRegister.singleton qEnc).basisOutcomeProjector 1
    have hPre {hi : ℕ} (hhi : hi < 2 ^ (D - d)) :=
      cCohShiftPre_mulVec_ket_act wHas wIdx wOut qEnc hd d hdLt δ hHas1 hw0 hq0 hhi
    have hqId (p : Fin (2 ^ D)) :
        Function.update (Function.update δ (wOut p) 1) qEnc 0 = Function.update δ (wOut p) 1 :=
      update_eq_self_of_zero ((Function.update_of_ne (hd.out_ne_q p).symm 1 δ).trans hq0)
    have ketEq {a b : ℕ} {ha : a < 2 ^ D} {hb : b < 2 ^ D} (h : a = b) :
        ket (Function.update δ (wOut ⟨a, ha⟩) 1) = ket (Function.update δ (wOut ⟨b, hb⟩) 1) :=
      congrArg (fun p ↦ ket (Function.update δ (wOut p) 1)) (Fin.ext h)
    have hpLo (q : Fin (2 ^ (D - (d + 1)))) : lo + 2 ^ d * (2 * q.val) < 2 ^ D :=
      shift_pos_lt (Nat.le_of_lt hdLt) hlo (hEv q)
    have htbLo (q : Fin (2 ^ (D - (d + 1)))) : (lo + 2 ^ d * (2 * q.val)).testBit d = false := by
      rw [testBit_lo_add_mul_two_pow hlo]; simp only [decide_eq_false_iff_not]; omega
    have hpHi (q : Fin (2 ^ (D - (d + 1)))) : (lo + 2 ^ d * (2 * q.val)) + 2 ^ d < 2 ^ D := by
      have heq : (lo + 2 ^ d * (2 * q.val)) + 2 ^ d = lo + 2 ^ d * (2 * q.val + 1) := by ring
      rw [heq]; exact shift_pos_lt (Nat.le_of_lt hdLt) hlo (hOd q)
    rcases bit_cases (δ (wIdx ⟨d, hdLt⟩)) with hu0 | hu1
    · have hs0 : (∑ q, F₁.mulVec (cPre.eval.1.mulVec (kIn (2 * q.val) (hEv q)))) = 0 :=
        Finset.sum_eq_zero fun q _ ↦ by
          dsimp only [F₁, cPre, kIn]
          rw [← Matrix.mulVec_mulVec, hPre (hEv q), ite_eq_right (hev q),
            hu0, add_zero, ket_projector_one, Function.update_self, ite_eq_right zero_ne_one,
            Matrix.mulVec_zero]
      have hs1 : (∑ q, F₁.mulVec (cPre.eval.1.mulVec (kIn (2 * q.val + 1) (hOd q)))) =
          ∑ q, kOut q :=
        Finset.sum_congr rfl fun q _ ↦ by
          dsimp only [F₁, cPre, kIn, kOut]
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
            hPre (hOd q), ite_eq_left (hod q), hu0, add_zero, ket_projector_one,
            Function.update_self, ite_eq_left rfl, ket_X, Function.update_self,
            CharTwo.add_self_eq_zero, Function.update_idem, hqId]
          have hFin1 : (⟨lo + 2 ^ d * (2 * q.val + 1), shift_pos_lt (Nat.le_of_lt hdLt) hlo
              (hOd q)⟩ : Fin (2 ^ D)) = if true then
              ⟨(lo + 2 ^ d * (2 * q.val)) + 2 ^ d, hpHi q⟩ else
              ⟨lo + 2 ^ d * (2 * q.val), hpLo q⟩ :=
            Fin.ext (by dsimp; ring)
          rw [hFin1]
          change cB.eval.1.mulVec (ket (Function.update δ (w 0 (if true then _ else _)) 1)) = _
          rw [barrelSwap_mulVec_ket_pair w hw d δ (fun _ p ↦ hw0 p) 0
            (hpLo q) (htbLo q) (hpHi q) true]
          exact ketEq (by dsimp [idxValPrefix, lo]; rw [ite_eq_right (by rw [hu0]; decide)]; ring)
      rw [hs0, hs1, zero_add]
    · have hs1 : (∑ q, F₁.mulVec (cPre.eval.1.mulVec (kIn (2 * q.val) (hEv q)))) = ∑ q, kOut q :=
        Finset.sum_congr rfl fun q _ ↦ by
          dsimp only [F₁, cPre, kIn, kOut]
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
            hPre (hEv q), ite_eq_right (hev q), hu1, zero_add, ket_projector_one,
            Function.update_self, ite_eq_left rfl, ket_X, Function.update_self,
            CharTwo.add_self_eq_zero, Function.update_idem, hqId]
          have hFin0 : (⟨lo + 2 ^ d * (2 * q.val), hpLo q⟩ : Fin (2 ^ D)) =
              if false then ⟨(lo + 2 ^ d * (2 * q.val)) + 2 ^ d, hpHi q⟩
              else ⟨lo + 2 ^ d * (2 * q.val), hpLo q⟩ := rfl
          rw [hFin0]
          change cB.eval.1.mulVec (ket (Function.update δ (w 0 (if false then _ else _)) 1)) = _
          rw [barrelSwap_mulVec_ket_pair w hw d δ (fun _ p ↦ hw0 p) 0
            (hpLo q) (htbLo q) (hpHi q) false]
          exact ketEq (by dsimp [idxValPrefix, lo]; rw [ite_eq_left hu1]; ring)
      have hs0 : (∑ q, F₁.mulVec (cPre.eval.1.mulVec (kIn (2 * q.val + 1) (hOd q)))) = 0 :=
        Finset.sum_eq_zero fun q _ ↦ by
          dsimp only [F₁, cPre, kIn]
          rw [← Matrix.mulVec_mulVec, hPre (hOd q), ite_eq_left (hod q),
            hu1, CharTwo.add_self_eq_zero, ket_projector_one, Function.update_self,
            ite_eq_right zero_ne_one, Matrix.mulVec_zero]
      rw [hs1, hs0, add_zero]
  · intro δ hHas0 hw0 hq0
    dsimp only [cPre, cB]
    rw[cCohShiftPre_mulVec_ket_inact wHas wIdx wOut qEnc hd d hdLt δ hHas0 hw0 hq0,
        Matrix.mulVec_smul, Matrix.mulVec_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        ket_projector_one, ite_eq_right (hq0.trans_ne zero_ne_one), Matrix.mulVec_zero,
        Matrix.mulVec_zero, zero_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        ket_projector_one, Function.update_self, ite_eq_left rfl, ket_X, Function.update_idem,
        Function.update_self, CharTwo.add_self_eq_zero, update_eq_self_of_zero hq0,
        barrelSwap_mulVec_ket_zero w hw d δ (fun _ p ↦ hw0 p)]
theorem subspaceStep_wCohShiftLevels {Var : Type} [Fintype Var] [DecidableEq Var]
    {D n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (wHas : Wire n) (wIdx : Fin D → Wire n) (wOut : Fin (2 ^ D) → Wire n) (qEnc : Wire n)
    (hd : WRouterDisj wHas wIdx wOut qEnc) :
    ∀ (m : ℕ) (hm : m ≤ D),
      SubspaceStep
        (wCohSuperOp wHas wIdx wOut qEnc 0 (Nat.zero_le D))
        (wCohSuperOp wHas wIdx wOut qEnc m hm)
        (wCohShiftLevels v wHas wIdx wOut qEnc hd.has_ne_q hd.idx_ne_q hd.out_inj hd.out_ne_q m hm)
  | 0, _ => by
      simpa only [wCohShiftLevels, Circuit.eval_identity, Submonoid.coe_one, Matrix.one_mul] using
        subspaceStep_of_circuit (Var := Var)
          (wCohSuperOp wHas wIdx wOut qEnc 0 (Nat.zero_le D)) (.identity : Circuit n)
  | d + 1, hdLt =>
      (subspaceStep_wCohShiftLevels v wHas wIdx wOut qEnc hd d (Nat.le_of_succ_le hdLt)).seq
        (subspaceStep_wCohShiftLevel v wHas wIdx wOut qEnc hd d hdLt)
theorem subspaceStep_wStateComputeCohGate1 (k : ℕ) {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (wHas : Wire n) (wIdx : Fin (k + 1) → Wire n) (wOut : Fin (2 ^ (k + 1)) → Wire n)
    (qEnc : Wire n) (hd : WRouterDisj wHas wIdx wOut qEnc)
    (R : Operator (2 ^ n)) (hSupp : SupportedOn (ValidWCohGateIn wOut qEnc) R) :
    SubspaceStep R ((uOneHotToggle wHas wIdx wOut hd.has_ne_out hd.idx_ne_out).1 * R)
      (wStateComputeCohGate1 k v wHas wIdx wOut qEnc) := by
  classical
  have hdP : WRouterDisjProp wHas wIdx wOut qEnc := hd.disjProp
  dsimp only [wStateComputeCohGate1]
  rw [dite_eq_left hdP]
  let w : Fin 1 → Fin (2 ^ (k + 1)) → Wire n := fun _ p ↦ wOut p
  have hw : WInj w := wInj_w1Of hdP.2.2.2.2.1
  let cTree := Circuit.CNOT wHas (wOut ⟨0, Nat.two_pow_pos (k + 1)⟩) (hdP.1 _) ;;ᶜ
    wTreePrefix 1 (k + 1) w hw (k + 1) le_rfl
  have hTreeEq : cTree.eval.1 * R =
      wCohSuperOp wHas wIdx wOut qEnc 0 (Nat.zero_le (k + 1)) * R := by
    refine hSupp _ _ fun δ hV ↦ ?_
    have hV' : (∀ p : Fin (2 ^ (k + 1)), δ (wOut p) = 0) ∧ δ qEnc = 0 := hV
    have ⟨hw0, hq0⟩ := hV'
    dsimp only [cTree, wCohSuperOp]
    rw [mkVecOp_mulVec_ket]
    dsimp only [wCohSuperVec]
    rw [ite_eq_left hV', eval_seq_mulVec]
    rcases bit_cases (δ wHas) with hHas0 | hHas1
    · have hne1 : ¬ (δ wHas = 1) := by rw [hHas0]; decide
      rw [ite_eq_right hne1, ket_CNOT_ctrl_zero _ hHas0,
        wTreePrefix_mulVec_ket_zero w hw δ (fun _ p ↦ hw0 p) (k + 1) le_rfl]
    · rw [ite_eq_left hHas1, ket_CNOT, hw0 ⟨0, Nat.two_pow_pos (k + 1)⟩, hHas1, zero_add]
      exact wSuperVec_bot_pub (fun _ ↦ (0 : Fin 1)) wIdx w hw qEnc δ (fun _ p ↦ hw0 p) hq0
  have hTopEq : wCohSuperOp wHas wIdx wOut qEnc (k + 1) le_rfl * R =
      (uOneHotToggle wHas wIdx wOut hd.has_ne_out hd.idx_ne_out).1 * R := by
    refine hSupp _ _ fun δ hV ↦ ?_
    have hV' : (∀ p : Fin (2 ^ (k + 1)), δ (wOut p) = 0) ∧ δ qEnc = 0 := hV
    have ⟨hw0, hq0⟩ := hV'
    dsimp only [wCohSuperOp]
    rw [mkVecOp_mulVec_ket, uOneHotToggle_mulVec_ket]
    dsimp only [wCohSuperVec, toggleOneHotBits]
    have hLt : idxValD wIdx δ < 2 ^ (k + 1) := idxValD_lt_two_pow wIdx δ
    rw [ite_eq_left hV', dite_eq_left hLt, hw0 ⟨idxValD wIdx δ, hLt⟩, zero_add]
    rcases bit_cases (δ wHas) with hHas0 | hHas1
    · have hne1 : ¬ (δ wHas = 1) := by rw [hHas0]; decide
      rw [ite_eq_right hne1, hHas0, update_eq_self_of_zero (hw0 _)]
    · rw [ite_eq_left hHas1, hHas1]
      exact wSuperVec_top_pub (fun _ ↦ (0 : Fin 1)) wIdx w qEnc δ (fun _ p ↦ hw0 p) hq0
  have sTree : SubspaceStep R (wCohSuperOp wHas wIdx wOut qEnc 0 (Nat.zero_le (k + 1)) * R)
      (.circuit cTree) :=
    subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) R cTree) hTreeEq
  have sShift := subspaceStep_mul_right R
    (subspaceStep_wCohShiftLevels v wHas wIdx wOut qEnc hd (k + 1) le_rfl)
  exact subspaceStep_congr_out (sTree.seq sShift) hTopEq
theorem subspaceStep_wStateUncomputeCohGate1 (k : ℕ) {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)] (v : Var)
    (wHas : Wire n) (wIdx : Fin (k + 1) → Wire n) (wOut : Fin (2 ^ (k + 1)) → Wire n)
    (hHasOut : ∀ j, wHas ≠ wOut j) (hIdxOut : ∀ d j, wIdx d ≠ wOut j)
    (hOutInj : ∀ i j, i ≠ j → wOut i ≠ wOut j)
    (R_clean : Operator (2 ^ n)) (hSupp : SupportedOn (ValidWCohGateClean wOut) R_clean) :
    SubspaceStep ((uOneHotToggle wHas wIdx wOut hHasOut hIdxOut).1 * R_clean) R_clean
      (wStateUncomputeCohGate1 k v wHas wIdx wOut) := by
  classical
  have hOutD : WRouterOutDisj wHas wIdx wOut := ⟨hHasOut, hIdxOut, hOutInj⟩
  dsimp only [wStateUncomputeCohGate1]
  rw [dite_eq_left hOutD]
  let w : Fin 1 → Fin (2 ^ (k + 1)) → Wire n := fun _ p ↦ wOut p
  have hw : WInj w := wInj_w1Of hOutD.2.2
  have huw : ∀ d b p, wIdx d ≠ w b p := fun d _ p ↦ hOutD.2.1 d p
  let p0 : Fin (2 ^ (k + 1)) := ⟨0, Nat.two_pow_pos (k + 1)⟩
  let cRoot := Circuit.CNOT wHas (wOut p0) (hOutD.1 p0)
  let P := ValidWCohGateClean wOut
  let act : BitAssignment n → Prop := fun δ ↦ δ wHas = 1
  let idOp : Operator (2 ^ n) :=
    mkVecOp fun δ ↦ if P δ ∧ ∀ b p, δ (w b p) = 0 then ket δ else 0
  have hRootEq : cRoot.eval.1 *
      oneHotOptPreOp P act (fun _ ↦ (0 : Fin 1)) wIdx w 0 (Nat.zero_le (k + 1)) = idOp := by
    apply matrix_ext_ket; intro δ
    simp only [← Matrix.mulVec_mulVec, oneHotOptPreOp, idOp, mkVecOp_mulVec_ket, oneHotOptPreVec]
    by_cases hV : P δ ∧ ∀ b p, δ (w b p) = 0
    · rw [ite_eq_left hV, ite_eq_left hV]
      rcases bit_cases (δ wHas) with hHas0 | hHas1
      · have hne1 : ¬ act δ := by dsimp [act]; rw [hHas0]; decide
        rw [ite_eq_right hne1]
        exact ket_CNOT_ctrl_zero _ hHas0
      · rw [ite_eq_left hHas1]
        have hpEq : (⟨idxValPrefix wIdx δ 0 (Nat.zero_le (k + 1)), Nat.lt_of_lt_of_le
            (idxValPrefix_lt_two_pow wIdx δ 0 (Nat.zero_le (k + 1))) (Nat.pow_le_pow_right
            (by omega) (Nat.zero_le (k + 1)))⟩ : Fin (2 ^ (k + 1))) = p0 := Fin.ext rfl
        rw [hpEq]
        dsimp only [cRoot, w]
        rw[ket_CNOT, Function.update_self, Function.update_of_ne (hOutD.1 p0), hHas1,
            CharTwo.add_self_eq_zero, Function.update_idem, update_eq_self_of_zero (hV.1 p0)]
    · rw [ite_eq_right hV, ite_eq_right hV, Matrix.mulVec_zero]
  have sRoot : SubspaceStep (oneHotOptPreOp P act (fun _ ↦ (0 : Fin 1)) wIdx w 0 (Nat.zero_le
      (k + 1))) idOp (.circuit cRoot) :=
    subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ cRoot) hRootEq
  have sTree := subspaceStep_mul_right R_clean (subspaceStep_wUncompTreeDyn_opt v P act (fun _
      ↦ (0 : Fin 1)) wIdx w hw huw sRoot (k + 1) le_rfl)
  have hInEq : (uOneHotToggle wHas wIdx wOut hHasOut hIdxOut).1 * R_clean =
      oneHotOptPreOp P act (fun _ ↦ (0 : Fin 1)) wIdx w (k + 1) le_rfl * R_clean := by
    refine hSupp _ _ fun δ hClean ↦ ?_
    have hV : P δ ∧ ∀ b p, δ (w b p) = 0 := ⟨hClean, fun _ p ↦ hClean p⟩
    have hLt : idxValD wIdx δ < 2 ^ (k + 1) := idxValD_lt_two_pow wIdx δ
    rw [uOneHotToggle_mulVec_ket, oneHotOptPreOp, mkVecOp_mulVec_ket]
    dsimp only [toggleOneHotBits, oneHotOptPreVec]
    rw [dite_eq_left hLt, ite_eq_left hV, hClean ⟨idxValD wIdx δ, hLt⟩, zero_add]
    rcases bit_cases (δ wHas) with hHas0 | hHas1
    · have hne1 : ¬ act δ := by dsimp [act]; rw [hHas0]; decide
      rw [ite_eq_right hne1, hHas0, update_eq_self_of_zero (hClean _)]
    · rw [ite_eq_left hHas1, hHas1]
      rfl
  have hOutEq : idOp * R_clean = R_clean := by
    have h1 := hSupp idOp (1 : Operator (2 ^ n)) fun δ hClean ↦ by
      have hV : P δ ∧ ∀ b p, δ (w b p) = 0 := ⟨hClean, fun _ p ↦ hClean p⟩
      dsimp only [idOp]
      rw [mkVecOp_mulVec_ket, ite_eq_left hV, Matrix.one_mulVec]
    rwa [Matrix.one_mul] at h1
  exact subspaceStep_congr_out (subspaceStep_congr_in hInEq sTree) hOutEq
/-- Symmetric clean-ancilla context extending `DiagCtxW` with coherent zero-gated
`Pow2` W-state routers. -/
inductive DiagCtxWG (M : ℕ) where
  | hole : DiagCtxWG M
  | cliffConj (c : CliffProg M) (K : DiagCtxWG M) : DiagCtxWG M
  | tempAnd (c₁ c₂ anc : Wire M) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
      (K : DiagCtxWG M) : DiagCtxWG M
  | wStateTree (k : ℕ) (wIdx : Fin (k + 1) → Wire M) (wOut : Fin (2 ^ (k + 1)) → Wire M)
      (qEnc : Wire M) (hd : DisjWUncond wIdx wOut qEnc)
      (K : DiagCtxWG M) : DiagCtxWG M
  | wStateTreeCohGate1 (k : ℕ) (wHas : Wire M) (wIdx : Fin (k + 1) → Wire M)
      (wOut : Fin (2 ^ (k + 1)) → Wire M) (qEnc : Wire M)
      (hd : DisjWCohGate1 wHas wIdx wOut qEnc)
      (K : DiagCtxWG M) : DiagCtxWG M
namespace DiagCtxWG
/-- Forward classical bit-state map of a `DiagCtxWG M` context. -/
def fwdBits {M : ℕ} : DiagCtxWG M → BitAssignment M → BitAssignment M
  | .hole, γ => γ
  | .cliffConj c K, γ => K.fwdBits (c.eval γ)
  | .tempAnd c₁ c₂ anc _ _ _ K, γ =>
      K.fwdBits (Function.update γ anc (γ anc + γ c₁ * γ c₂))
  | .wStateTree _ wIdx wOut _ _ K, γ =>
      let j : Fin (2 ^ _) := ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩
      K.fwdBits (Function.update γ (wOut j) (γ (wOut j) + 1))
  | .wStateTreeCohGate1 _ wHas wIdx wOut _ _ K, γ =>
      let j : Fin (2 ^ _) := ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩
      K.fwdBits (Function.update γ (wOut j) (γ (wOut j) + γ wHas))
/-- Clean-ancilla precondition along `DiagCtxWG M`. -/
def ValidAt {M : ℕ} : DiagCtxWG M → BitAssignment M → Prop
  | .hole, _ => True
  | .cliffConj c K, γ => K.ValidAt (c.eval γ)
  | .tempAnd c₁ c₂ anc _ _ _ K, γ =>
      γ anc = 0 ∧ K.ValidAt (Function.update γ anc (γ anc + γ c₁ * γ c₂))
  | .wStateTree _ wIdx wOut qEnc _ K, γ =>
      ((∀ l, γ (wOut l) = 0) ∧ γ qEnc = 0) ∧
      let j : Fin (2 ^ _) := ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩
      K.ValidAt (Function.update γ (wOut j) (γ (wOut j) + 1))
  | .wStateTreeCohGate1 _ wHas wIdx wOut qEnc _ K, γ =>
      ((∀ l, γ (wOut l) = 0) ∧ γ qEnc = 0) ∧
      let j : Fin (2 ^ _) := ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩
      K.ValidAt (Function.update γ (wOut j) (γ (wOut j) + γ wHas))
/-- Combined clean-ancilla + hole-invariant precondition along `DiagCtxWG M`. -/
def ValidAtWith {M : ℕ} (InvHole : BitAssignment M → Prop) :
    DiagCtxWG M → BitAssignment M → Prop
  | .hole, γ => InvHole γ
  | .cliffConj c K, γ => ValidAtWith InvHole K (c.eval γ)
  | .tempAnd c₁ c₂ anc _ _ _ K, γ =>
      γ anc = 0 ∧ ValidAtWith InvHole K (Function.update γ anc (γ anc + γ c₁ * γ c₂))
  | .wStateTree _ wIdx wOut qEnc _ K, γ =>
      (∀ l, γ (wOut l) = 0) ∧ γ qEnc = 0 ∧
      let j : Fin (2 ^ _) := ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩
      ValidAtWith InvHole K (Function.update γ (wOut j) (γ (wOut j) + 1))
  | .wStateTreeCohGate1 _ wHas wIdx wOut qEnc _ K, γ =>
      (∀ l, γ (wOut l) = 0) ∧ γ qEnc = 0 ∧
      let j : Fin (2 ^ _) := ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩
      ValidAtWith InvHole K (Function.update γ (wOut j) (γ (wOut j) + γ wHas))
theorem validAtWith_of_validAt {M : ℕ} {InvHole : BitAssignment M → Prop} :
    ∀ (K : DiagCtxWG M) {γ : BitAssignment M},
      K.ValidAt γ → InvHole (K.fwdBits γ) → K.ValidAtWith InvHole γ
  | .hole, _, _, hI => hI
  | .cliffConj _ K, _, hV, hI => validAtWith_of_validAt K hV hI
  | .tempAnd _ _ _ _ _ _ K, _, ⟨h0, hV⟩, hI =>
      ⟨h0, validAtWith_of_validAt K hV hI⟩
  | .wStateTree _ _ _ _ _ K, _, ⟨⟨hOut0, hq0⟩, hV⟩, hI =>
      ⟨hOut0, hq0, validAtWith_of_validAt K hV hI⟩
  | .wStateTreeCohGate1 _ _ _ _ _ _ K, _, ⟨⟨hOut0, hq0⟩, hV⟩, hI =>
      ⟨hOut0, hq0, validAtWith_of_validAt K hV hI⟩
/-- Exact `T`-gate count added by a `DiagCtxWG M` wrapper. -/
def countT {M : ℕ} : DiagCtxWG M → ℕ
  | .hole => 0
  | .cliffConj _ K => K.countT
  | .tempAnd _ _ _ _ _ _ K => 4 + K.countT
  | .wStateTree k _ _ _ _ K => 4 * (2 ^ k - 1) + K.countT
  | .wStateTreeCohGate1 k _ _ _ _ _ K => 2 * (2 ^ (k + 1) + k) + K.countT
theorem wStateTreeCohGate1_step {M : ℕ} (k : ℕ) (wHas : Wire M) (wIdx : Fin (k + 1) → Wire M)
    (wOut : Fin (2 ^ (k + 1)) → Wire M) (qEnc : Wire M)
    (hd : DisjWCohGate1 wHas wIdx wOut qEnc) (body : DiagCtxWG M) (γ : BitAssignment M)
    (hOut0 : ∀ j : Fin (2 ^ (k + 1)), γ (wOut j) = 0) (hq0 : γ qEnc = 0) : ∃ γ' :
    BitAssignment M, (DiagCtxWG.wStateTreeCohGate1 k wHas wIdx wOut qEnc hd body).fwdBits γ =
    body.fwdBits γ' ∧ (body.ValidAt γ' → (DiagCtxWG.wStateTreeCohGate1 k wHas wIdx wOut qEnc
    hd body).ValidAt γ) ∧ (∀ j : Fin (2 ^ (k + 1)), γ' (wOut j) = if j.val = bitsVal (fun i :
    Fin (k + 1) ↦ γ (wIdx i)) then γ wHas else 0) ∧
    (∀ w : Wire M, (∀ j : Fin (2 ^ (k + 1)), w ≠ wOut j) → γ' w = γ w) := by
  let j₀ : Fin (2 ^ (k + 1)) := ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩
  let γ' : BitAssignment M := Function.update γ (wOut j₀) (γ (wOut j₀) + γ wHas)
  have hj₀_val : j₀.val = bitsVal (fun i : Fin (k + 1) ↦ γ (wIdx i)) :=
    idxValD_eq_bitsVal (k + 1) wIdx γ
  refine ⟨γ', rfl, fun hV ↦ ⟨⟨hOut0, hq0⟩, hV⟩, fun j ↦ ?_, fun w hw ↦ ?_⟩
  · dsimp only [γ']
    by_cases hj : j.val = bitsVal (fun i : Fin (k + 1) ↦ γ (wIdx i))
    · have hjeq : j = j₀ := Fin.ext (hj.trans hj₀_val.symm)
      rw [ite_eq_left hj, hjeq, Function.update_self, hOut0 j₀, zero_add]
    · have hjne : j ≠ j₀ := fun h ↦ hj ((congrArg Fin.val h).trans hj₀_val)
      have hwne : wOut j ≠ wOut j₀ := fun h ↦ hjne (hd.2.2.2.2.1 h)
      rw [ite_eq_right hj, Function.update_of_ne hwne, hOut0 j]
  · exact Function.update_of_ne (hw j₀) _ _
end DiagCtxWG
/-- `DiagCtxWG M` predicate certifying all wires written by `toDynWG` have index `≥ base`. -/
def DiagCtxWGWritesAbove {M : ℕ} (base : ℕ) : DiagCtxWG M → Prop
  | .hole => True
  | .cliffConj c K => CliffWritesAbove base c ∧ DiagCtxWGWritesAbove base K
  | .tempAnd _ _ anc _ _ _ K => base ≤ anc.val ∧ DiagCtxWGWritesAbove base K
  | .wStateTree _ _ wOut _ _ K =>
      (∀ l, base ≤ (wOut l).val) ∧ DiagCtxWGWritesAbove base K
  | .wStateTreeCohGate1 _ _ _ wOut _ _ K =>
      (∀ l, base ≤ (wOut l).val) ∧ DiagCtxWGWritesAbove base K
/-- Semantic commutation predicate for `DiagCtxWG M` with `U₀ : Unitary (2 ^ n)`. -/
def DiagCtxWGCommutesWith {M n : ℕ} (rComb : QRegister M n) (U₀ : Unitary (2 ^ n)) :
    DiagCtxWG M → Prop
  | .hole => True
  | .cliffConj c K₁ =>
      (c.inv.onRegister rComb).toCircuit.eval * U₀ = U₀ * (c.inv.onRegister rComb).toCircuit.eval ∧
      DiagCtxWGCommutesWith rComb U₀ K₁
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁ =>
      let cToff := Circuit.gate TOFF (QRegister.triple (rComb c₁) (rComb c₂) (rComb anc)
          (rComb.wires.injective.ne h₁₂) (rComb.wires.injective.ne h₁a)
          (rComb.wires.injective.ne h₂a))
      cToff.eval * U₀ = U₀ * cToff.eval ∧
      (∀ g' g : Fin (2 ^ n), U₀.1 g' g ≠ 0 →
        basisBits n g' (rComb anc) = basisBits n g (rComb anc)) ∧
      DiagCtxWGCommutesWith rComb U₀ K₁
  | .wStateTree k wIdx wOut _ hd K₁ =>
      let hdN := wUncondDisjProp_onRegister rComb hd
      let uOH := uOneHotUncond (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l)) hdN.1
      uOH * U₀ = U₀ * uOH ∧
      (∀ (l : Fin (2 ^ (k + 1))) (g' g : Fin (2 ^ n)), U₀.1 g' g ≠ 0 →
        basisBits n g' (rComb (wOut l)) = basisBits n g (rComb (wOut l))) ∧
      DiagCtxWGCommutesWith rComb U₀ K₁
  | .wStateTreeCohGate1 k wHas wIdx wOut _ hd K₁ =>
      let hdN := wRouterDisj_onRegister rComb hd
      let uOH := uOneHotToggle (rComb wHas) (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l))
        hdN.has_ne_out hdN.idx_ne_out
      uOH * U₀ = U₀ * uOH ∧
      (∀ (l : Fin (2 ^ (k + 1))) (g' g : Fin (2 ^ n)), U₀.1 g' g ≠ 0 →
        basisBits n g' (rComb (wOut l)) = basisBits n g (rComb (wOut l))) ∧
      DiagCtxWGCommutesWith rComb U₀ K₁
theorem comm_embedUnitary_uOneHotToggle {n kAct D : ℕ} (rAct : QRegister kAct n)
    (V : Unitary (2 ^ kAct)) (wHasN : Wire n) (wIdxN : Fin D → Wire n)
    (wOutN : Fin (2 ^ D) → Wire n) (hHasOut : ∀ j, wHasN ≠ wOutN j)
    (hIdxOut : ∀ d j, wIdxN d ≠ wOutN j)
    (hOutNotAct : ∀ j : Fin (2 ^ D), wOutN j ∉ Set.range rAct.wires) (hHasPres : ∀ (g : Fin (2
    ^ n)) (y : Fin (2 ^ kAct)), V.1 y (rAct.extractIndex g) ≠ 0 → basisBits n
    (rAct.replaceIndex g y) wHasN = basisBits n g wHasN) (hIdxPres : ∀ (d : Fin D) (g : Fin (2
    ^ n)) (y : Fin (2 ^ kAct)), V.1 y (rAct.extractIndex g) ≠ 0 → basisBits n
    (rAct.replaceIndex g y) (wIdxN d) = basisBits n g (wIdxN d)) : uOneHotToggle wHasN wIdxN
    wOutN hHasOut hIdxOut * rAct.embedUnitary V = rAct.embedUnitary V * uOneHotToggle wHasN
    wIdxN wOutN hHasOut hIdxOut := by
  let uOH := uOneHotToggle wHasN wIdxN wOutN hHasOut hIdxOut
  apply Subtype.ext; apply matrix_ext_ket; intro β
  simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  let g := (basisBitsEquiv n).symm β
  have hgβ : basisBits n g = β := (basisBitsEquiv n).apply_symm_apply β
  have hLtβ : idxValD wIdxN β < 2 ^ D := idxValD_lt_two_pow wIdxN β
  let j₀ : Fin (2 ^ D) := ⟨idxValD wIdxN β, hLtβ⟩
  let w := wOutN j₀
  have hw : w ∉ Set.range rAct.wires := hOutNotAct j₀
  let b := β w + β wHasN
  let β' := Function.update β w b
  let g' := (basisBitsEquiv n).symm β'
  have hg'β' : basisBits n g' = β' := (basisBitsEquiv n).apply_symm_apply β'
  have hExEq : rAct.extractIndex g' = rAct.extractIndex g := by
    apply (basisBitsEquiv kAct).injective
    funext i
    change basisBits kAct (rAct.extractIndex g') i = basisBits kAct (rAct.extractIndex g) i
    rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex, hg'β', hgβ]
    dsimp only [β']
    exact Function.update_of_ne (fun h ↦ hw ⟨i, h⟩) _ _
  change uOH.1.mulVec ((rAct.embedUnitary V).1.mulVec (ket β)) =
    (rAct.embedUnitary V).1.mulVec (uOH.1.mulVec (ket β))
  have hToggleβ : toggleOneHotBits wHasN wIdxN wOutN β = β' := by
    dsimp only [toggleOneHotBits]
    rw [dite_eq_left hLtβ]
  rw [uOneHotToggle_mulVec_ket wHasN wIdxN wOutN hHasOut hIdxOut β, hToggleβ]
  conv_rhs =>
    rw [p2d_ket_eq_single β', QRegister.embedUnitary_val,
        embedMatrix_mulVec_single_sum rAct V.1 g', hExEq]
  conv_lhs =>
    rw [p2d_ket_eq_single β, QRegister.embedUnitary_val,
        embedMatrix_mulVec_single_sum rAct V.1 g, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  by_cases hnz : V.1 y (rAct.extractIndex g) = 0
  · simp [hnz]
  · rw [Matrix.mulVec_smul]
    refine congrArg (V.1 y (rAct.extractIndex g) • ·) ?_
    let gy := rAct.replaceIndex g y
    have hLtGy : idxValD wIdxN (basisBits n gy) < 2 ^ D := idxValD_lt_two_pow wIdxN (basisBits n gy)
    have hjEq : (⟨idxValD wIdxN (basisBits n gy), hLtGy⟩ : Fin (2 ^ D)) = j₀ := by
      apply Fin.ext
      dsimp only [j₀]
      rw [idxValD_eq_bitsVal, idxValD_eq_bitsVal]
      refine congrArg bitsVal (funext fun d ↦ ?_)
      rw [hIdxPres d g y hnz, hgβ]
    have hToggleGy : toggleOneHotBits wHasN wIdxN wOutN (basisBits n gy) =
        Function.update (basisBits n gy) w (basisBits n gy w + basisBits n gy wHasN) := by
      dsimp only [toggleOneHotBits]
      rw [dite_eq_left hLtGy, hjEq]
    rw [single_eq_ket_basisBits gy,
        uOneHotToggle_mulVec_ket wHasN wIdxN wOutN hHasOut hIdxOut (basisBits n gy),
        hToggleGy, p2d_ket_eq_single]
    refine congrArg (fun idx ↦ (Pi.single idx (1 : ℂ) : Fin (2 ^ n) → ℂ)) ?_
    apply eq_of_basisBits_eq; intro q
    rw [basisBits_symm_apply_at]
    by_cases hqw : q = w
    · rw [hqw, Function.update_self, rAct.basisBits_replaceIndex_of_not_mem g' y w hw,
          rAct.basisBits_replaceIndex_of_not_mem g y w hw, hHasPres g y hnz, hg'β']
      dsimp only [β', b]
      rw [Function.update_self, hgβ]
    · rw [Function.update_of_ne hqw]
      by_cases hqD : q ∈ Set.range rAct.wires
      · obtain ⟨i, rfl⟩ := hqD
        rw [QRegister.basisBits_replaceIndex_apply, QRegister.basisBits_replaceIndex_apply]
      · rw[rAct.basisBits_replaceIndex_of_not_mem g y q hqD,
          rAct.basisBits_replaceIndex_of_not_mem g' y q hqD, hg'β']
        dsimp only [β']
        rw [Function.update_of_ne hqw, hgβ]
theorem diagCtxWGWritesAbove_to_commutesWith {M n kAct : ℕ}
    (rAct : QRegister kAct n) (V : Unitary (2 ^ kAct))
    (rComb : QRegister M n) (base : ℕ)
    (hOutNotAct : ∀ idx : Wire M, base ≤ idx.val → rComb idx ∉ Set.range rAct.wires)
    (hCombPres : ∀ (idx : Wire M) (g : Fin (2 ^ n)) (y : Fin (2 ^ kAct)),
      V.1 y (rAct.extractIndex g) ≠ 0 →
      basisBits n (rAct.replaceIndex g y) (rComb idx) = basisBits n g (rComb idx)) :
    ∀ {K : DiagCtxWG M}, DiagCtxWGWritesAbove base K →
      DiagCtxWGCommutesWith rComb (rAct.embedUnitary V) K
  | .hole, _ => trivial
  | .cliffConj _ _, ⟨hc, hK⟩ =>
      ⟨cliffWritesAbove_comm_embedUnitary rAct V rComb base hOutNotAct hCombPres hc.inv,
       diagCtxWGWritesAbove_to_commutesWith rAct V rComb base hOutNotAct hCombPres hK⟩
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a _, ⟨hanc, hK⟩ => by
      refine ⟨?_, ?_,
        diagCtxWGWritesAbove_to_commutesWith rAct V rComb base hOutNotAct hCombPres hK⟩
      · exact comm_embedUnitary_of_update_outside rAct V
          (Circuit.gate TOFF
            (QRegister.triple (rComb c₁) (rComb c₂) (rComb anc)
              (rComb.wires.injective.ne h₁₂)
              (rComb.wires.injective.ne h₁a)
              (rComb.wires.injective.ne h₂a)))
          (rComb anc) (hOutNotAct anc hanc)
          (fun β ↦ β (rComb c₁) * β (rComb c₂))
          (fun β ↦ ket_TOFF (rComb c₁) (rComb c₂) (rComb anc)
            (rComb.wires.injective.ne h₁₂)
            (rComb.wires.injective.ne h₁a)
            (rComb.wires.injective.ne h₂a) β)
          (fun g y hnz ↦ by rw [hCombPres c₁ g y hnz, hCombPres c₂ g y hnz])
      · intro g' g hnz
        have hnot := hOutNotAct anc hanc
        rw [QRegister.embedUnitary_val, QRegister.embedMatrix_apply] at hnz
        split_ifs at hnz with henv
        · exact ((rAct.basisSplit_environment_eq_iff g' g).mp henv) (rComb anc) hnot
        · simp at hnz
  | .wStateTree _ wIdx wOut _ hd _, ⟨hOut, hK⟩ => by
      refine ⟨?_, ?_,
        diagCtxWGWritesAbove_to_commutesWith rAct V rComb base hOutNotAct hCombPres hK⟩
      · exact comm_embedUnitary_uOneHotUncond rAct V (fun d ↦ rComb (wIdx d))
          (fun l ↦ rComb (wOut l)) (wUncondDisjProp_onRegister rComb hd).1
          (fun l ↦ hOutNotAct (wOut l) (hOut l)) (fun d g y hnz ↦ hCombPres (wIdx d) g y hnz)
      · intro l g' g hnz
        have hnot := hOutNotAct (wOut l) (hOut l)
        rw [QRegister.embedUnitary_val, QRegister.embedMatrix_apply] at hnz
        split_ifs at hnz with henv
        · exact ((rAct.basisSplit_environment_eq_iff g' g).mp henv) (rComb (wOut l)) hnot
        · simp at hnz
  | .wStateTreeCohGate1 _ wHas wIdx wOut _ hd _, ⟨hOut, hK⟩ => by
      have hdN := wRouterDisj_onRegister rComb hd
      refine ⟨?_, ?_,
        diagCtxWGWritesAbove_to_commutesWith rAct V rComb base hOutNotAct hCombPres hK⟩
      · exact comm_embedUnitary_uOneHotToggle rAct V (rComb wHas) (fun d ↦ rComb (wIdx d))
          (fun l ↦ rComb (wOut l)) hdN.has_ne_out hdN.idx_ne_out
          (fun l ↦ hOutNotAct (wOut l) (hOut l)) (fun g y hnz ↦ hCombPres wHas g y hnz)
          (fun d g y hnz ↦ hCombPres (wIdx d) g y hnz)
      · intro l g' g hnz
        have hnot := hOutNotAct (wOut l) (hOut l)
        rw [QRegister.embedUnitary_val, QRegister.embedMatrix_apply] at hnz
        split_ifs at hnz with henv
        · exact ((rAct.basisSplit_environment_eq_iff g' g).mp henv) (rComb (wOut l)) hnot
        · simp at hnz
/-! ## Section 2C: Shifted Partner Slot, `17`-Wire Index Selector, & `224 T`
`ctxShiftedPartnerFast` -/
theorem wSlot1Core_ofFin_val : (wSlot1Core (QRegExt.ofFin posCoreWires)).val = 3949 := rfl
theorem wSlot2Core_ofFin_val : (wSlot2Core (QRegExt.ofFin posCoreWires)).val = 3950 := rfl
theorem rAnchorIdx_ofFin_val_local (i : Fin 8) :
    (rAnchorIdx (QRegExt.ofFin posCoreWires) i).val = 3968 + i.val := by
  revert i; decide
theorem rPartnerIdx_ofFin_val_local (i : Fin 8) :
    (rPartnerIdx (QRegExt.ofFin posCoreWires) i).val = 3976 + i.val := by
  revert i; decide
theorem rElecSlot_ofFin_val_local (e : Fin 218) (j : Fin 18) :
    (rElecSlot (QRegExt.ofFin posCoreWires) e j).val = 18 * e.val + j.val := rfl
/-- Shifted partner slot index in `Fin 218` for the anchored `(rAct, rAnchor18)` frame:
when `c1 = 0` (`wSlot1Core = 0`) and `u + 1 = vAnc` (`u = aliasPartner217 (regVal rPartnerIdx)`),
partner `u + 1` collided with `e = coinBarrelIdxFast (le_refl 80)` on `{c2 = 0}` and resides at
`slot[0]`; otherwise partner `u + 1` remains at `slot[u + 1]`. -/
def shiftedPartnerSlotFast (γ : BitAssignment posCoreWires) : Fin 218 :=
  let rCoreL := QRegExt.ofFin posCoreWires
  let c1 := γ (wSlot1Core rCoreL)
  let vAnc := bitsVal (fun i : Fin 8 ↦ γ (rAnchorIdx rCoreL i))
  let u := aliasPartner217 (bitsVal (fun i : Fin 8 ↦ γ (rPartnerIdx rCoreL i)))
  if decide (c1 = 0 ∧ u + 1 = vAnc) then ⟨0, by decide⟩
  else ⟨u + 1, by
    have := aliasPartner217_lt (bitsVal_lt_two_pow (fun i : Fin 8 ↦ γ (rPartnerIdx rCoreL i)))
    omega⟩
theorem shiftedPartnerSlotFast_congr {γ₁ γ₂ : BitAssignment posCoreWires} (hc1 : γ₁
    (wSlot1Core (QRegExt.ofFin posCoreWires)) = γ₂ (wSlot1Core (QRegExt.ofFin
    posCoreWires))) (hAnc : ∀ i : Fin 8, γ₁ (rAnchorIdx (QRegExt.ofFin posCoreWires) i) = γ₂
    (rAnchorIdx (QRegExt.ofFin posCoreWires) i)) (hPart : ∀ i : Fin 8, γ₁ (rPartnerIdx
    (QRegExt.ofFin posCoreWires) i) = γ₂ (rPartnerIdx (QRegExt.ofFin posCoreWires) i)) :
    shiftedPartnerSlotFast γ₁ = shiftedPartnerSlotFast γ₂ := by
  have hA : (fun i : Fin 8 ↦ γ₁ (rAnchorIdx (QRegExt.ofFin posCoreWires) i)) =
      (fun i : Fin 8 ↦ γ₂ (rAnchorIdx (QRegExt.ofFin posCoreWires) i)) := funext hAnc
  have hP : (fun i : Fin 8 ↦ γ₁ (rPartnerIdx (QRegExt.ofFin posCoreWires) i)) =
      (fun i : Fin 8 ↦ γ₂ (rPartnerIdx (QRegExt.ofFin posCoreWires) i)) := funext hPart
  dsimp only [shiftedPartnerSlotFast]
  simp only [hc1, hA, hP]
theorem shiftedPartnerSlotFast_congr_outside {γ₁ γ₂ : BitAssignment posCoreWires}
    (h : ∀ w : Wire posCoreWires, 3949 ≤ w.val → w.val < 3984 → γ₁ w = γ₂ w) :
    shiftedPartnerSlotFast γ₁ = shiftedPartnerSlotFast γ₂ :=
  shiftedPartnerSlotFast_congr
    (h _ (by rw [wSlot1Core_ofFin_val]) (by rw [wSlot1Core_ofFin_val]; omega))
    (fun i ↦ h _ (by rw [rAnchorIdx_ofFin_val_local]; omega)
                 (by rw [rAnchorIdx_ofFin_val_local]; have := i.isLt; omega))
    (fun i ↦ h _ (by rw [rPartnerIdx_ofFin_val_local]; omega)
                 (by rw [rPartnerIdx_ofFin_val_local]; have := i.isLt; omega))
theorem shiftedPartnerSlotFast_eq_on_c2_zero
    (γ : BitAssignment posCoreWires)
    (hc2 : γ (wSlot2Core (QRegExt.ofFin posCoreWires)) = 0) :
    let u := aliasPartner217 (bitsVal (fun i : Fin 8 ↦ γ (rPartnerIdx (QRegExt.ofFin
        posCoreWires) i)))
    let e := (coinBarrelIdxFast (le_refl 80) γ).val
    (shiftedPartnerSlotFast γ).val = (if u + 1 = e then 0 else u + 1) ∧
    (shiftedPartnerSlotFast γ).val ≠ e := by
  intro u e
  have hu_lt : u < 217 :=
    aliasPartner217_lt (bitsVal_lt_two_pow (fun i : Fin 8 ↦ γ (rPartnerIdx (QRegExt.ofFin
        posCoreWires) i)))
  let vAnc := bitsVal (fun i : Fin 8 ↦ γ (rAnchorIdx (QRegExt.ofFin posCoreWires) i))
  have hc1_wire : FullSysCatSegmentBridge.iSlot1 80 =
      wSlot1Core (QRegExt.ofFin posCoreWires) := rfl
  have hc2_wire : FullSysCatSegmentBridge.iSlot2 80 =
      wSlot2Core (QRegExt.ofFin posCoreWires) := rfl
  have hu8_eq : CoinDispatchedBarrel288.Internal.bitsVal (fun j : Fin 8 ↦
      γ ⟨3968 + j.val, by
        have : posCoreWires = 4034 := rfl
        omega⟩) = vAnc := by
    change bitsVal _ = bitsVal _
    refine congrArg bitsVal (funext fun j ↦ congrArg γ (Fin.ext ?_))
    exact (rAnchorIdx_ofFin_val_local j).symm
  have he_val : e = if γ (wSlot1Core (QRegExt.ofFin posCoreWires)) = 1 then 0
      else if vAnc < 218 then vAnc else 0 := by
    dsimp only [e, coinBarrelIdxFast]
    rw [hc1_wire, hc2_wire, hc2, ite_eq_left rfl, hu8_eq]
    split_ifs <;> rfl
  have hs_val : (shiftedPartnerSlotFast γ).val =
      if γ (wSlot1Core (QRegExt.ofFin posCoreWires)) = 0 ∧ u + 1 = vAnc then 0 else u + 1 := by
    dsimp only [shiftedPartnerSlotFast]
    by_cases h : γ (wSlot1Core (QRegExt.ofFin posCoreWires)) = 0 ∧ u + 1 = vAnc
    · rw [ite_eq_left (decide_eq_true h), ite_eq_left h]
    · have hdec : ¬ (decide (γ (wSlot1Core (QRegExt.ofFin posCoreWires)) = 0 ∧ u + 1 = vAnc) =
        true) := by
        rw [decide_eq_true_iff]; exact h
      rw [ite_eq_right hdec, ite_eq_right h]
  change (shiftedPartnerSlotFast γ).val = (if u + 1 = e then 0 else u + 1) ∧
    (shiftedPartnerSlotFast γ).val ≠ e
  rw [hs_val, he_val]
  rcases bit_cases (γ (wSlot1Core (QRegExt.ofFin posCoreWires))) with hc1 | hc1
  · have h01 : ¬ ((0 : ZMod 2) = 1) := by decide
    simp only [hc1, h01, true_and, ↓reduceIte]
    by_cases hv : vAnc < 218 <;> by_cases huv : u + 1 = vAnc <;> simp [hv, huv] <;> omega
  · have h10 : ¬ ((1 : ZMod 2) = 0) := by decide
    rw [hc1, ite_eq_right (fun h ↦ h10 h.1), ite_eq_left rfl]
    exact ⟨by simp, Nat.succ_ne_zero u⟩
/-- Active `.hole` invariant on `n` qubits for the `64 × 4` `shiftedPartnerSlotFast` W-state
  context. -/
def InvHoleShifted218 {n mScr : ℕ} (hm : 75 ≤ mScr) (rCore : QRegister posCoreWires n)
    (rScr : QRegister mScr n) (β : BitAssignment n) : Prop :=
  let s₀ := shiftedPartnerSlotFast (fun w ↦ β (rCore w))
  (∀ l : Fin 64, β (rScr ⟨l.val, by omega⟩) = if l.val = s₀.val % 64 then 1 else 0) ∧
  (∀ h : Fin 4, β (rScr ⟨64 + h.val, by omega⟩) = if h.val = s₀.val / 64 then 1 else 0) ∧
  β (rScr ⟨69, by omega⟩) = 0 ∧
  (∀ r : Fin 4, β (p2dSubReg rScr 70 4 (by omega) r) = 0) ∧
  β (rScr ⟨74, by omega⟩) = 0
/-- `17`-wire read-only index register inside `posCoreWires`:
wire `0 = wSlot1Core` (`3949`), wires `1..8 = rAnchorIdx` (`3968..3975`), wires `9..16 =
rPartnerIdx` (`3976..3983`). -/
def rShiftedIdx17OfFin : QRegister 17 posCoreWires :=
  ⟨⟨fun idx ↦
      if h0 : idx.val = 0 then wSlot1Core (QRegExt.ofFin posCoreWires)
      else if h9 : idx.val < 9 then rAnchorIdx (QRegExt.ofFin posCoreWires) ⟨idx.val - 1, by
          omega⟩
      else rPartnerIdx (QRegExt.ofFin posCoreWires) ⟨idx.val - 9, by omega⟩,
    fun a b hab ↦ by
      have ha := a.isLt; have hb := b.isLt
      have hv := congrArg Fin.val hab
      dsimp only at hv
      by_cases ha0 : a.val = 0 <;> by_cases hb0 : b.val = 0
      · exact Fin.ext (by omega)
      · by_cases hb9 : b.val < 9
        · simp only [ha0, hb0, hb9, ↓reduceDIte, wSlot1Core_ofFin_val, rAnchorIdx_ofFin_val_local]
            at hv; omega
        · simp only [ha0, hb0, hb9, ↓reduceDIte, wSlot1Core_ofFin_val, rPartnerIdx_ofFin_val_local]
            at hv; omega
      · by_cases ha9 : a.val < 9
        · simp only [ha0, ha9, hb0, ↓reduceDIte, wSlot1Core_ofFin_val, rAnchorIdx_ofFin_val_local]
            at hv; omega
        · simp only [ha0, ha9, hb0, ↓reduceDIte, wSlot1Core_ofFin_val, rPartnerIdx_ofFin_val_local]
            at hv; omega
      · by_cases ha9 : a.val < 9 <;> by_cases hb9 : b.val < 9
        · simp only [ha0, ha9, hb0, hb9, ↓reduceDIte, rAnchorIdx_ofFin_val_local] at hv; exact
            Fin.ext (by omega)
        · simp only [ha0, ha9, hb0, hb9, ↓reduceDIte, rAnchorIdx_ofFin_val_local,
            rPartnerIdx_ofFin_val_local] at hv; omega
        · simp only [ha0, ha9, hb0, hb9, ↓reduceDIte, rAnchorIdx_ofFin_val_local,
            rPartnerIdx_ofFin_val_local] at hv; omega
        · simp only [ha0, ha9, hb0, hb9, ↓reduceDIte, rPartnerIdx_ofFin_val_local] at hv; exact
            Fin.ext (by omega)⟩⟩
/-- Composition of `rCore` with `rShiftedIdx17OfFin`. -/
def rShiftedIdx17Core {n : ℕ} (rCore : QRegister posCoreWires n) : QRegister 17 n :=
  rCore.compose rShiftedIdx17OfFin
@[simp] theorem rShiftedIdx17OfFin_zero :
    rShiftedIdx17OfFin ⟨0, by decide⟩ = wSlot1Core (QRegExt.ofFin posCoreWires) := rfl
@[simp] theorem rShiftedIdx17OfFin_wires_zero :
    rShiftedIdx17OfFin.wires 0 = wSlot1Core (QRegExt.ofFin posCoreWires) := rfl
theorem rShiftedIdx17OfFin_anc (i : Fin 8) :
    rShiftedIdx17OfFin ⟨1 + i.val, by omega⟩ = rAnchorIdx (QRegExt.ofFin posCoreWires) i := by
  have hi := i.isLt
  change (if h0 : 1 + i.val = 0 then wSlot1Core (QRegExt.ofFin posCoreWires)
    else if h9 : 1 + i.val < 9 then rAnchorIdx (QRegExt.ofFin posCoreWires) ⟨(1 + i.val) - 1, by
        omega⟩
    else rPartnerIdx (QRegExt.ofFin posCoreWires) ⟨(1 + i.val) - 9, by omega⟩) = _
  have h0 : ¬ (1 + i.val = 0) := by omega
  have h9 : 1 + i.val < 9 := by omega
  simp only [h0, h9, ↓reduceDIte]
  exact congrArg (rAnchorIdx (QRegExt.ofFin posCoreWires)).wires (Fin.ext (by dsimp; omega))
theorem rShiftedIdx17OfFin_part (i : Fin 8) :
    rShiftedIdx17OfFin ⟨9 + i.val, by omega⟩ = rPartnerIdx (QRegExt.ofFin posCoreWires) i := by
  have hi := i.isLt
  change (if h0 : 9 + i.val = 0 then wSlot1Core (QRegExt.ofFin posCoreWires)
    else if h9 : 9 + i.val < 9 then rAnchorIdx (QRegExt.ofFin posCoreWires) ⟨(9 + i.val) - 1, by
        omega⟩
    else rPartnerIdx (QRegExt.ofFin posCoreWires) ⟨(9 + i.val) - 9, by omega⟩) = _
  have h0 : ¬ (9 + i.val = 0) := by omega
  have h9 : ¬ (9 + i.val < 9) := by omega
  simp only [h0, h9, ↓reduceDIte]
  exact congrArg (rPartnerIdx (QRegExt.ofFin posCoreWires)).wires (Fin.ext (by dsimp; omega))
/-- Pure `8`-bit `ZMod 2` formula for `w = aliasPartner217 (bitsVal b) + 1`, sharing `car2 = b 0 *
  b 1`
with `(b 0 + 1) * (b 1 + 1) = car2 + (b 1 + b 0) + 1`. -/
def pureW (b : Fin 8 → ZMod 2) : Fin 8 → ZMod 2 :=
  let car2 := b 0 * b 1
  let w1 := b 1 + b 0
  let nb2 := b 2 + 1
  let nb5 := b 5 + 1
  let t96 := car2 + w1 + 1
  let t97 := t96 * nb2 + 1
  let t98 := b 3 * b 4
  let t99 := t98 * t97 + 1
  let t100 := nb5 * t99 + 1
  let t101 := b 6 * b 7
  let ge217 := t101 * t100
  let car3 := car2 * b 2
  let car4 := car3 * b 3
  let car5 := car4 * b 4
  let car6 := car5 * b 5
  let car7 := car6 * b 6
  fun k ↦ match k.val with
    | 0 => b 0 + 1
    | 1 => w1
    | 2 => b 2 + car2
    | 3 => b 3 + car3
    | 4 => b 4 + car4
    | 5 => b 5 + car5
    | 6 => b 6 + car6
    | _ => b 7 + ge217 + car7
theorem pureW_bitsVal_basisBits_8 :
    ∀ x : Fin (2 ^ 8), bitsVal (pureW (basisBits 8 x)) = aliasPartner217 (bitsVal (basisBits 8 x))
        + 1 := by
  decide
theorem pureW_bitsVal_eq (b : Fin 8 → ZMod 2) :
    bitsVal (pureW b) = aliasPartner217 (bitsVal b) + 1 := by
  have hEqB : ∀ x : Fin (2 ^ 8), (basisBitsEquiv 8) x = basisBits 8 x := fun _ ↦ rfl
  rw [← (basisBitsEquiv 8).apply_symm_apply b, hEqB]
  exact pureW_bitsVal_basisBits_8 _
theorem bitsVal_inj_8 {u v : Fin 8 → ZMod 2} : bitsVal u = bitsVal v ↔ u = v :=
  ⟨bitsVal_injective, congrArg bitsVal⟩
/-- Pure `8`-bit `ZMod 2` formula for `j[0..8)` computed by `ctxShiftedPartner2D_64x4_W`. -/
def pureShiftedIdx8 (c1 : ZMod 2) (a b : Fin 8 → ZMod 2) : Fin 8 → ZMod 2 :=
  let w := pureW b
  let nc1 := c1 + 1
  let xnor : Fin 8 → ZMod 2 := fun k ↦ w k + a k + 1
  let p0 := nc1 * xnor 0
  let p1 := p0 * xnor 1
  let p2 := p1 * xnor 2
  let p3 := p2 * xnor 3
  let p4 := p3 * xnor 4
  let p5 := p4 * xnor 5
  let p6 := p5 * xnor 6
  let neq := p6 * xnor 7 + 1
  fun k ↦ neq * w k
theorem zmod2_mul_eq_one_iff (x y : ZMod 2) : x * y = 1 ↔ x = 1 ∧ y = 1 := by
  rcases bit_cases x with rfl | rfl <;> rcases bit_cases y with rfl | rfl <;> decide
theorem zmod2_xnor_eq_one_iff (x y : ZMod 2) : x + y + 1 = 1 ↔ x = y := by
  rcases bit_cases x with rfl | rfl <;> rcases bit_cases y with rfl | rfl <;> decide
theorem zmod2_add_one_eq_one_iff (x : ZMod 2) : x + 1 = 1 ↔ x = 0 := by
  rcases bit_cases x with rfl | rfl <;> decide
theorem pureShiftedIdx8_bitsVal_eq (γCore : BitAssignment posCoreWires) :
    let c1 := γCore (wSlot1Core (QRegExt.ofFin posCoreWires))
    let a : Fin 8 → ZMod 2 := fun i ↦ γCore (rAnchorIdx (QRegExt.ofFin posCoreWires) i)
    let b : Fin 8 → ZMod 2 := fun i ↦ γCore (rPartnerIdx (QRegExt.ofFin posCoreWires) i)
    bitsVal (pureShiftedIdx8 c1 a b) = (shiftedPartnerSlotFast γCore).val := by
  intro c1 a b
  let w := pureW b
  let nc1 := c1 + 1
  let xnor : Fin 8 → ZMod 2 := fun k ↦ w k + a k + 1
  let eqProd := (((((((nc1 * xnor 0) * xnor 1) * xnor 2) * xnor 3) * xnor 4) * xnor 5) * xnor 6) *
      xnor 7
  have hnc1 : nc1 = 1 ↔ c1 = 0 := zmod2_add_one_eq_one_iff c1
  have hxnor : ∀ k : Fin 8, xnor k = 1 ↔ w k = a k := fun k ↦ zmod2_xnor_eq_one_iff (w k) (a k)
  have hProdOne : eqProd = 1 ↔ (c1 = 0 ∧ w = a) := by
    dsimp only [eqProd]
    simp only [zmod2_mul_eq_one_iff, hnc1, hxnor]
    constructor
    · rintro ⟨⟨⟨⟨⟨⟨⟨⟨hc1, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩
      refine ⟨hc1, funext fun k ↦ ?_⟩
      fin_cases k
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact h4
      · exact h5
      · exact h6
      · exact h7
    · rintro ⟨hc1, hwa⟩
      rw [hwa]
      exact ⟨⟨⟨⟨⟨⟨⟨⟨hc1, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
  have hWA : (w = a) ↔ aliasPartner217 (bitsVal b) + 1 = bitsVal a := by
    rw [← bitsVal_inj_8, pureW_bitsVal_eq]
  dsimp only [shiftedPartnerSlotFast]
  by_cases hCond : c1 = 0 ∧ aliasPartner217 (bitsVal b) + 1 = bitsVal a
  · rw [ite_eq_left (decide_eq_true hCond)]
    have hEq1 : eqProd = 1 := hProdOne.mpr ⟨hCond.1, hWA.mpr hCond.2⟩
    have hj0 : pureShiftedIdx8 c1 a b = fun _ ↦ 0 := by
      funext k; dsimp only [pureShiftedIdx8]
      change (eqProd + 1) * w k = 0
      rw [hEq1]; simp
    rw [hj0]; rfl
  · have hDec : ¬ (decide (c1 = 0 ∧ aliasPartner217 (bitsVal b) + 1 = bitsVal a) = true) :=
      fun hd ↦ hCond (of_decide_eq_true hd)
    rw [ite_eq_right hDec]
    have hEq0 : eqProd = 0 := by
      rcases bit_cases eqProd with h0 | h1
      · exact h0
      · exact absurd ⟨(hProdOne.mp h1).1, hWA.mp (hProdOne.mp h1).2⟩ hCond
    have hjw : pureShiftedIdx8 c1 a b = w := by
      funext k; dsimp only [pureShiftedIdx8]
      change (eqProd + 1) * w k = w k
      rw [hEq0]; simp
    rw [hjw, pureW_bitsVal_eq]
/-- Combined `133`-wire register concatenating `rShiftedIdx17Core` (`17` wires) with
`rScr[0..116)`. -/
def rComb133 {n mScr : ℕ} (hm : 116 ≤ mScr) (rCore : QRegister posCoreWires n)
    (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rScr) : QRegister 133 n :=
  (rShiftedIdx17Core rCore).concat (p2dSubReg rScr 0 116 hm) (by
    rw [QRegister.disjoint_iff]
    intro i j h
    have hj : p2dSubReg rScr 0 116 hm j = rScr ⟨j.val, by omega⟩ :=
      congrArg rScr.wires (Fin.ext (by dsimp [p2dSubReg]; omega))
    exact hCS.ne (rShiftedIdx17OfFin i) ⟨j.val, by omega⟩ (h.trans hj))
theorem rComb133_apply_lt {n mScr : ℕ} (hm : 116 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (idx : Wire 133) (hlt : idx.val < 17) :
    rComb133 hm rCore rScr hCS idx = rShiftedIdx17Core rCore ⟨idx.val, hlt⟩ := by
  dsimp only [rComb133]
  have hEq : idx = Fin.castAdd 116 ⟨idx.val, hlt⟩ := Fin.ext rfl
  exact (congrArg (rComb133 hm rCore rScr hCS).wires hEq).trans (QRegister.concat_apply_left
    (rShiftedIdx17Core rCore) (p2dSubReg rScr 0 116 hm) _ ⟨idx.val, hlt⟩)
theorem rComb133_apply_ge {n mScr : ℕ} (hm : 116 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (idx : Wire 133) (hge : 17 ≤ idx.val) :
    rComb133 hm rCore rScr hCS idx = rScr ⟨idx.val - 17, by omega⟩ := by
  dsimp only [rComb133]
  let j : Fin 116 := ⟨idx.val - 17, by have := idx.isLt; omega⟩
  have hEq : idx = Fin.natAdd 17 j := Fin.ext (by dsimp [j]; omega)
  have h1 : rComb133 hm rCore rScr hCS idx = rComb133 hm rCore rScr hCS (Fin.natAdd 17 j) :=
    congrArg (rComb133 hm rCore rScr hCS).wires hEq
  have h2 : rComb133 hm rCore rScr hCS (Fin.natAdd 17 j) = p2dSubReg rScr 0 116 hm j :=
    QRegister.concat_apply_right (rShiftedIdx17Core rCore) (p2dSubReg rScr 0 116 hm) _ j
  have h3 : p2dSubReg rScr 0 116 hm j = rScr ⟨idx.val - 17, by omega⟩ :=
    congrArg rScr.wires (Fin.ext (by dsimp [p2dSubReg, j]; omega))
  exact h1.trans (h2.trans h3)
/-- `11`-AND `8`-bit `ZMod 2` formula for `w = aliasPartner217 (bitsVal b) + 1`,
factoring `ge217 + car7 = b 6 * ((b 7 * t100) + car6)` to save `1` AND (`4 T`). -/
def pureWFast (b : Fin 8 → ZMod 2) : Fin 8 → ZMod 2 :=
  let car2 := b 0 * b 1
  let w1 := b 1 + b 0
  let nb2 := b 2 + 1
  let nb5 := b 5 + 1
  let t96 := car2 + w1 + 1
  let t97 := t96 * nb2 + 1
  let t98 := b 3 * b 4
  let t99 := t98 * t97 + 1
  let t100 := nb5 * t99 + 1
  let car3 := car2 * b 2
  let car4 := car3 * b 3
  let car5 := car4 * b 4
  let car6 := car5 * b 5
  let u1 := b 7 * t100
  let u2 := u1 + car6
  let geXorCar7 := b 6 * u2
  fun k ↦ match k.val with
    | 0 => b 0 + 1
    | 1 => w1
    | 2 => b 2 + car2
    | 3 => b 3 + car3
    | 4 => b 4 + car4
    | 5 => b 5 + car5
    | 6 => b 6 + car6
    | _ => b 7 + geXorCar7
private theorem pureWFast_bit7_aux (b6 b7 t100 car6 : ZMod 2) :
    b7 + b6 * (b7 * t100 + car6) = b7 + b6 * b7 * t100 + car6 * b6 := by
  ring
theorem pureWFast_eq_pureW (b : Fin 8 → ZMod 2) : pureWFast b = pureW b := by
  funext ⟨k, hk⟩
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact pureWFast_bit7_aux (b 6) (b 7) _ _
/-- Intended wire value table on `Wire 133` after computing wires `92 .. 132` from `γ₀`. -/
def spec133 (γ₀ : BitAssignment 133) (w : Wire 133) : ZMod 2 :=
  let c1 := γ₀ ⟨0, by decide⟩
  let a : Fin 8 → ZMod 2 := fun i ↦ γ₀ ⟨1 + i.val, by omega⟩
  let b : Fin 8 → ZMod 2 := fun i ↦ γ₀ ⟨9 + i.val, by omega⟩
  let car2 := b 0 * b 1
  let w1 := b 1 + b 0
  let nb2 := b 2 + 1
  let nb5 := b 5 + 1
  let t96 := car2 + w1 + 1
  let t97 := t96 * nb2 + 1
  let t98 := b 3 * b 4
  let t99 := t98 * t97 + 1
  let t100 := nb5 * t99 + 1
  let car3 := car2 * b 2
  let car4 := car3 * b 3
  let car5 := car4 * b 4
  let car6 := car5 * b 5
  let u1 := b 7 * t100
  let u2 := u1 + car6
  let geXorCar7 := b 6 * u2
  let wVec := pureWFast b
  let nc1 := c1 + 1
  let xnor : Fin 8 → ZMod 2 := fun k ↦ wVec k + a k + 1
  let p0 := nc1 * xnor 0
  let p1 := p0 * xnor 1
  let p2 := p1 * xnor 2
  let p3 := p2 * xnor 3
  let p4 := p3 * xnor 4
  let p5 := p4 * xnor 5
  let p6 := p5 * xnor 6
  let neq := p6 * xnor 7 + 1
  match w.val with
  | 92 => car2 | 93 => w1 | 94 => nb2 | 95 => nb5
  | 96 => t96 | 97 => t97 | 98 => t98 | 99 => t99 | 100 => t100
  | 101 => car3 | 102 => car4 | 103 => car5 | 104 => car6
  | 105 => u1 | 106 => u2 | 107 => geXorCar7
  | 108 => wVec 0 | 109 => wVec 1 | 110 => wVec 2 | 111 => wVec 3
  | 112 => wVec 4 | 113 => wVec 5 | 114 => wVec 6 | 115 => wVec 7
  | 116 => nc1
  | 117 => xnor 0 | 118 => xnor 1 | 119 => xnor 2 | 120 => xnor 3
  | 121 => xnor 4 | 122 => xnor 5 | 123 => xnor 6 | 124 => xnor 7
  | 125 => p0 | 126 => p1 | 127 => p2 | 128 => p3
  | 129 => p4 | 130 => p5 | 131 => p6 | 132 => neq
  | _ => γ₀ w
theorem spec133_of_lt_92 (γ₀ : BitAssignment 133) (w : Wire 133) (hw : w.val < 92) :
    spec133 γ₀ w = γ₀ w := by
  dsimp [spec133]
  split <;> first | rfl | omega
/-- Predicate asserting that scratch wires `17 .. 132` of `Wire 133` are initialized to `0`. -/
def CleanScr116 (γ : BitAssignment 133) : Prop := ∀ w : Wire 133, 17 ≤ w.val → γ w = 0
/-- Hole invariant on `133`-wire `rComb133` produced by `ctxShiftedPartnerFast`:
`uLo` (`17..80`) is one-hot at `s₀ % 64`, `uHi` (`81..84`) is one-hot at `s₀ / 64`, and
`rScr[69..75)` (`wires 86..91`) remain `0`. -/
def InvShifted64x4Fast (γ : BitAssignment 133) : Prop :=
  let sVal := bitsVal (pureShiftedIdx8 (γ ⟨0, by decide⟩)
    (fun i ↦ γ ⟨1 + i.val, by omega⟩) (fun i ↦ γ ⟨9 + i.val, by omega⟩))
  (∀ (l : ℕ) (_hl : l < 64), γ ⟨17 + l, by omega⟩ = if l = sVal % 64 then 1 else 0) ∧
  (∀ (h : ℕ) (_hh : h < 4), γ ⟨81 + h, by omega⟩ = if h = sVal / 64 then 1 else 0) ∧
  (∀ (t : ℕ) (_ht : t < 6), γ ⟨86 + t, by omega⟩ = 0)
/-- Intermediate prefix-evaluation invariant up to wire `m` on `Wire 133`. -/
def AtStage133 (γ₀ : BitAssignment 133) (m : ℕ) (γ : BitAssignment 133) : Prop :=
    (∀ w : Wire 133, w.val < m → γ w = spec133 γ₀ w) ∧ (∀ w : Wire 133, m ≤ w.val → γ w = 0)
/-- Suffix validity and postcondition invariant from stage `m` onward on `Wire 133`. -/
def RunFrom133 (γ₀ : BitAssignment 133) (m : ℕ) (K : DiagCtxWG 133) : Prop :=
  ∀ γ : BitAssignment 133, AtStage133 γ₀ m γ → K.ValidAt γ ∧ InvShifted64x4Fast (K.fwdBits γ)
theorem atStage133_succ {γ₀ γ : BitAssignment 133} {m : ℕ} (hm : m < 133)
    (hAt : AtStage133 γ₀ m γ) (val : ZMod 2) (hVal : spec133 γ₀ ⟨m, hm⟩ = val) :
    AtStage133 γ₀ (m + 1) (Function.update γ ⟨m, hm⟩ val) := by
  refine ⟨fun w hw ↦ ?_, fun w hw ↦ ?_⟩
  · by_cases hwm : w = ⟨m, hm⟩
    · subst hwm; rw [Function.update_self, hVal]
    · have hlt : w.val < m := by
        have hne : w.val ≠ m := fun heq ↦ hwm (Fin.ext heq)
        omega
      rw [Function.update_of_ne hwm]
      exact hAt.1 w hlt
  · have hne : w ≠ ⟨m, hm⟩ := wire_ne_of_gt (by dsimp; omega)
    rw [Function.update_of_ne hne]
    exact hAt.2 w (by omega)
/-- Clifford gadget writing `src + 1` into clean wire `dst` on `Wire 133`. -/
def cliffSetNot133 (src dst : Wire 133) (hs : src.val < dst.val) : CliffProg 133 :=
  .seq (.cnot src dst (wire_ne_of_lt hs)) (.x dst)
/-- Clifford gadget writing `s₁ + s₂` into clean wire `dst` on `Wire 133`. -/
def cliffSetXor133 (s₁ s₂ dst : Wire 133) (h₁ : s₁.val < dst.val) (h₂ : s₂.val < dst.val) :
    CliffProg 133 := .seq (.cnot s₁ dst (wire_ne_of_lt h₁)) (.cnot s₂ dst (wire_ne_of_lt h₂))
/-- Clifford gadget writing `s₁ + s₂ + 1` into clean wire `dst` on `Wire 133`. -/
def cliffSetXnor133 (s₁ s₂ dst : Wire 133)
    (h₁ : s₁.val < dst.val) (h₂ : s₂.val < dst.val) : CliffProg 133 :=
  .seq (.cnot s₁ dst (wire_ne_of_lt h₁)) (.seq (.cnot s₂ dst (wire_ne_of_lt h₂)) (.x dst))
/-- `DiagCtxWG 133` wrapper writing `src + 1` to wire `m`. -/
def ctxNot133 (m : ℕ) (hm : m < 133) (src : Wire 133) (hs : src.val < m) (K : DiagCtxWG 133) :
    DiagCtxWG 133 := .cliffConj (cliffSetNot133 src ⟨m, hm⟩ hs) K
/-- `DiagCtxWG 133` wrapper writing `s₁ + s₂` to wire `m`. -/
def ctxXor133 (m : ℕ) (hm : m < 133) (s₁ s₂ : Wire 133) (h₁ : s₁.val < m) (h₂ : s₂.val < m)
    (K : DiagCtxWG 133) : DiagCtxWG 133 := .cliffConj (cliffSetXor133 s₁ s₂ ⟨m, hm⟩ h₁ h₂) K
/-- `DiagCtxWG 133` wrapper writing `s₁ + s₂ + 1` to wire `m`. -/
def ctxXnor133 (m : ℕ) (hm : m < 133) (s₁ s₂ : Wire 133) (h₁ : s₁.val < m) (h₂ : s₂.val < m)
    (K : DiagCtxWG 133) : DiagCtxWG 133 := .cliffConj (cliffSetXnor133 s₁ s₂ ⟨m, hm⟩ h₁ h₂) K
/-- `DiagCtxWG 133` wrapper computing temporary AND `c₁ * c₂` onto clean wire `m` (`4 T`). -/
def ctxAnd133 (m : ℕ) (hm : m < 133) (c₁ c₂ : Wire 133) (h₁₂ : c₁ ≠ c₂)
    (h₁ : c₁.val < m) (h₂ : c₂.val < m) (K : DiagCtxWG 133) : DiagCtxWG 133 :=
  .tempAnd c₁ c₂ ⟨m, hm⟩ h₁₂ (wire_ne_of_lt h₁) (wire_ne_of_lt h₂) K
/-- `DiagCtxWG 133` wrapper computing temporary NAND `c₁ * c₂ + 1` onto clean wire `m` (`4 T`). -/
def ctxNand133 (m : ℕ) (hm : m < 133) (c₁ c₂ : Wire 133) (h₁₂ : c₁ ≠ c₂)
    (h₁ : c₁.val < m) (h₂ : c₂.val < m) (K : DiagCtxWG 133) : DiagCtxWG 133 :=
  .tempAnd c₁ c₂ ⟨m, hm⟩ h₁₂ (wire_ne_of_lt h₁) (wire_ne_of_lt h₂) (.cliffConj (.x ⟨m, hm⟩) K)
theorem runFrom133_ctxNot {γ₀ : BitAssignment 133} (m : ℕ) (hm : m < 133)
    (src : Wire 133) (hs : src.val < m) {K : DiagCtxWG 133}
    (hSpec : spec133 γ₀ ⟨m, hm⟩ = spec133 γ₀ src + 1)
    (hNext : RunFrom133 γ₀ (m + 1) K) :
    RunFrom133 γ₀ m (ctxNot133 m hm src hs K) := fun γ hAt ↦ by
  have hm0 : γ ⟨m, hm⟩ = 0 := hAt.2 ⟨m, hm⟩ le_rfl
  have hEval : (cliffSetNot133 src ⟨m, hm⟩ hs).eval γ =
      Function.update γ ⟨m, hm⟩ (γ src + 1) := by
    dsimp [cliffSetNot133, CliffProg.eval]
    rw [Function.update_idem, Function.update_self, hm0, zero_add]
  change K.ValidAt ((cliffSetNot133 src ⟨m, hm⟩ hs).eval γ) ∧
    InvShifted64x4Fast (K.fwdBits ((cliffSetNot133 src ⟨m, hm⟩ hs).eval γ))
  rw [hEval]
  exact hNext _ (atStage133_succ hm hAt _ (hSpec.trans (congrArg (· + 1) (hAt.1 src hs).symm)))
theorem runFrom133_ctxXor {γ₀ : BitAssignment 133} (m : ℕ) (hm : m < 133)
    (s₁ s₂ : Wire 133) (h₁ : s₁.val < m) (h₂ : s₂.val < m) {K : DiagCtxWG 133}
    (hSpec : spec133 γ₀ ⟨m, hm⟩ = spec133 γ₀ s₁ + spec133 γ₀ s₂)
    (hNext : RunFrom133 γ₀ (m + 1) K) :
    RunFrom133 γ₀ m (ctxXor133 m hm s₁ s₂ h₁ h₂ K) := fun γ hAt ↦ by
  have hm0 : γ ⟨m, hm⟩ = 0 := hAt.2 ⟨m, hm⟩ le_rfl
  have hEval : (cliffSetXor133 s₁ s₂ ⟨m, hm⟩ h₁ h₂).eval γ =
      Function.update γ ⟨m, hm⟩ (γ s₁ + γ s₂) := by
    dsimp [cliffSetXor133, CliffProg.eval]
    rw [Function.update_idem, Function.update_self,
        Function.update_of_ne (wire_ne_of_lt h₂), hm0, zero_add]
  change K.ValidAt ((cliffSetXor133 s₁ s₂ ⟨m, hm⟩ h₁ h₂).eval γ) ∧
    InvShifted64x4Fast (K.fwdBits ((cliffSetXor133 s₁ s₂ ⟨m, hm⟩ h₁ h₂).eval γ))
  rw [hEval]
  refine hNext _ (atStage133_succ hm hAt _ ?_)
  rw [hSpec, hAt.1 s₁ h₁, hAt.1 s₂ h₂]
theorem runFrom133_ctxXnor {γ₀ : BitAssignment 133} (m : ℕ) (hm : m < 133)
    (s₁ s₂ : Wire 133) (h₁ : s₁.val < m) (h₂ : s₂.val < m) {K : DiagCtxWG 133}
    (hSpec : spec133 γ₀ ⟨m, hm⟩ = spec133 γ₀ s₁ + spec133 γ₀ s₂ + 1)
    (hNext : RunFrom133 γ₀ (m + 1) K) :
    RunFrom133 γ₀ m (ctxXnor133 m hm s₁ s₂ h₁ h₂ K) := fun γ hAt ↦ by
  have hm0 : γ ⟨m, hm⟩ = 0 := hAt.2 ⟨m, hm⟩ le_rfl
  have hne₂ : s₂ ≠ ⟨m, hm⟩ := wire_ne_of_lt (a := s₂) (b := ⟨m, hm⟩) h₂
  have hEval : (cliffSetXnor133 s₁ s₂ ⟨m, hm⟩ h₁ h₂).eval γ =
      Function.update γ ⟨m, hm⟩ (γ s₁ + γ s₂ + 1) := by
    funext w
    dsimp [cliffSetXnor133, CliffProg.eval]
    by_cases hw : w = ⟨m, hm⟩
    · subst hw
      simp only [Function.update_self, Function.update_of_ne hne₂, hm0, zero_add]
    · simp only [Function.update_of_ne hw]
  change K.ValidAt ((cliffSetXnor133 s₁ s₂ ⟨m, hm⟩ h₁ h₂).eval γ) ∧
    InvShifted64x4Fast (K.fwdBits ((cliffSetXnor133 s₁ s₂ ⟨m, hm⟩ h₁ h₂).eval γ))
  rw [hEval]
  refine hNext _ (atStage133_succ hm hAt _ ?_)
  rw [hSpec, hAt.1 s₁ h₁, hAt.1 s₂ h₂]
theorem runFrom133_ctxAnd {γ₀ : BitAssignment 133} (m : ℕ) (hm : m < 133)
    (c₁ c₂ : Wire 133) (h₁₂ : c₁ ≠ c₂) (h₁ : c₁.val < m) (h₂ : c₂.val < m) {K : DiagCtxWG 133}
    (hSpec : spec133 γ₀ ⟨m, hm⟩ = spec133 γ₀ c₁ * spec133 γ₀ c₂)
    (hNext : RunFrom133 γ₀ (m + 1) K) :
    RunFrom133 γ₀ m (ctxAnd133 m hm c₁ c₂ h₁₂ h₁ h₂ K) := fun γ hAt ↦ by
  have hm0 : γ ⟨m, hm⟩ = 0 := hAt.2 ⟨m, hm⟩ le_rfl
  change (γ ⟨m, hm⟩ = 0 ∧ K.ValidAt (Function.update γ ⟨m, hm⟩ (γ ⟨m, hm⟩ + γ c₁ * γ c₂))) ∧
    InvShifted64x4Fast (K.fwdBits (Function.update γ ⟨m, hm⟩ (γ ⟨m, hm⟩ + γ c₁ * γ c₂)))
  rw [hm0, zero_add]
  have hRes := hNext _ (atStage133_succ hm hAt (γ c₁ * γ c₂)
    (by rw [hSpec, hAt.1 c₁ h₁, hAt.1 c₂ h₂]))
  exact ⟨⟨rfl, hRes.1⟩, hRes.2⟩
theorem runFrom133_ctxNand {γ₀ : BitAssignment 133} (m : ℕ) (hm : m < 133)
    (c₁ c₂ : Wire 133) (h₁₂ : c₁ ≠ c₂) (h₁ : c₁.val < m) (h₂ : c₂.val < m) {K : DiagCtxWG 133}
    (hSpec : spec133 γ₀ ⟨m, hm⟩ = spec133 γ₀ c₁ * spec133 γ₀ c₂ + 1)
    (hNext : RunFrom133 γ₀ (m + 1) K) :
    RunFrom133 γ₀ m (ctxNand133 m hm c₁ c₂ h₁₂ h₁ h₂ K) := fun γ hAt ↦ by
  have hm0 : γ ⟨m, hm⟩ = 0 := hAt.2 ⟨m, hm⟩ le_rfl
  let γ₁ := Function.update γ ⟨m, hm⟩ (γ ⟨m, hm⟩ + γ c₁ * γ c₂)
  have hγ₁ : (CliffProg.x ⟨m, hm⟩).eval γ₁ = Function.update γ ⟨m, hm⟩ (γ c₁ * γ c₂ + 1) := by
    dsimp [γ₁, CliffProg.eval]
    rw [Function.update_idem, Function.update_self, hm0, zero_add]
  change (γ ⟨m, hm⟩ = 0 ∧ K.ValidAt ((CliffProg.x ⟨m, hm⟩).eval γ₁)) ∧
    InvShifted64x4Fast (K.fwdBits ((CliffProg.x ⟨m, hm⟩).eval γ₁))
  rw [hγ₁]
  have hRes := hNext _ (atStage133_succ hm hAt (γ c₁ * γ c₂ + 1)
    (by rw [hSpec, hAt.1 c₁ h₁, hAt.1 c₂ h₂]))
  exact ⟨⟨hm0, hRes.1⟩, hRes.2⟩
theorem shFast_hdLo :
    DisjWCohGate1 (M := 133)
      ⟨132, by decide⟩
      (fun j : Fin 6 ↦ ⟨108 + j.val, by omega⟩)
      (fun k : Fin (2 ^ 6) ↦ ⟨17 + k.val, by omega⟩)
      ⟨85, by decide⟩ :=
  ⟨fun k ↦ wire_ne_of_gt (by dsimp; have := k.isLt; omega),
   by decide,
   fun _ k ↦ wire_ne_of_gt (by dsimp; have := k.isLt; omega),
   fun _ ↦ wire_ne_of_gt (by dsimp; omega),
   fun _ _ h ↦ Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega),
   fun k ↦ wire_ne_of_lt (by dsimp; have := k.isLt; omega)⟩
theorem shFast_hdHi :
    DisjWCohGate1 (M := 133)
      ⟨132, by decide⟩
      (fun j : Fin 2 ↦ ⟨114 + j.val, by omega⟩)
      (fun k : Fin (2 ^ 2) ↦ ⟨81 + k.val, by omega⟩)
      ⟨85, by decide⟩ :=
  ⟨fun k ↦ wire_ne_of_gt (by dsimp; have := k.isLt; omega),
   by decide,
   fun _ k ↦ wire_ne_of_gt (by dsimp; have := k.isLt; omega),
   fun _ ↦ wire_ne_of_gt (by dsimp; omega),
   fun _ _ h ↦ Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega),
   fun k ↦ wire_ne_of_lt (by dsimp; have := k.isLt; omega)⟩
/-- Zero-`T` Clifford slot-0 toggle flipping `wHas = 132` (`neq`) to `eqProd = neq + 1` and
toggling `uLo[0]` (`wire 17`) and `uHi[0]` (`wire 81`) when `eqProd = 1`. -/
def cliffSlot0Toggle133 : CliffProg 133 :=
  .seq (.x ⟨132, by decide⟩)
    (.seq (.cnot ⟨132, by decide⟩ ⟨17, by decide⟩ (by decide))
      (.cnot ⟨132, by decide⟩ ⟨81, by decide⟩ (by decide)))
/-- Coherent zero-gated `64 × 4` unary W-state tree decoder (`138 + 10 = 148 T`) + slot-0 CNOTs. -/
def ctxShiftedTreesFast133 : DiagCtxWG 133 :=
  .wStateTreeCohGate1 5 ⟨132, by decide⟩ (fun j ↦ ⟨108 + j.val, by omega⟩)
    (fun k ↦ ⟨17 + k.val, by omega⟩) ⟨85, by decide⟩ shFast_hdLo
    (.wStateTreeCohGate1 1 ⟨132, by decide⟩ (fun j ↦ ⟨114 + j.val, by omega⟩)
      (fun k ↦ ⟨81 + k.val, by omega⟩) ⟨85, by decide⟩ shFast_hdHi
      (.cliffConj cliffSlot0Toggle133 .hole))
theorem cliffSlot0Toggle133_eval_apply (γ : BitAssignment 133) (w : Wire 133) :
    cliffSlot0Toggle133.eval γ w =
      if w = ⟨81, by decide⟩ then γ ⟨81, by decide⟩ + (γ ⟨132, by decide⟩ + 1)
      else if w = ⟨17, by decide⟩ then γ ⟨17, by decide⟩ + (γ ⟨132, by decide⟩ + 1)
      else if w = ⟨132, by decide⟩ then γ ⟨132, by decide⟩ + 1
      else γ w := by
  dsimp only [cliffSlot0Toggle133, CliffProg.eval]
  by_cases hw81 : w = ⟨81, by decide⟩
  · subst hw81
    simp only [↓reduceIte, Function.update_self]
    have h81_17 : (⟨81, by decide⟩ : Wire 133) ≠ ⟨17, by decide⟩ := by decide
    have h81_132 : (⟨81, by decide⟩ : Wire 133) ≠ ⟨132, by decide⟩ := by decide
    have h132_17 : (⟨132, by decide⟩ : Wire 133) ≠ ⟨17, by decide⟩ := by decide
    rw [Function.update_of_ne h81_17, Function.update_of_ne h81_132,
        Function.update_of_ne h132_17, Function.update_self]
  · simp only [hw81, ↓reduceIte, Function.update_of_ne hw81]
    by_cases hw17 : w = ⟨17, by decide⟩
    · subst hw17
      simp only [↓reduceIte, Function.update_self]
      have h17_132 : (⟨17, by decide⟩ : Wire 133) ≠ ⟨132, by decide⟩ := by decide
      rw [Function.update_of_ne h17_132]
    · simp only [hw17, ↓reduceIte, Function.update_of_ne hw17]
      by_cases hw132 : w = ⟨132, by decide⟩
      · subst hw132; simp only [↓reduceIte, Function.update_self]
      · simp only [hw132, ↓reduceIte, Function.update_of_ne hw132]
theorem runFrom_trees_fast (γ₀ : BitAssignment 133) (hγ₀ : CleanScr116 γ₀) :
    RunFrom133 γ₀ 133 ctxShiftedTreesFast133 := fun γ hAt ↦ by
  let wHas : Wire 133 := ⟨132, by decide⟩
  let addrLo : Fin 6 → Wire 133 := fun j ↦ ⟨108 + j.val, by omega⟩
  let outLo : Fin (2 ^ 6) → Wire 133 := fun k ↦ ⟨17 + k.val, by omega⟩
  let addrHi : Fin 2 → Wire 133 := fun j ↦ ⟨114 + j.val, by omega⟩
  let outHi : Fin (2 ^ 2) → Wire 133 := fun k ↦ ⟨81 + k.val, by omega⟩
  let qEnc : Wire 133 := ⟨85, by decide⟩
  let body2 : DiagCtxWG 133 := .cliffConj cliffSlot0Toggle133 .hole
  let body1 : DiagCtxWG 133 := .wStateTreeCohGate1 1 wHas addrHi outHi qEnc shFast_hdHi body2
  have hγ_spec : ∀ w : Wire 133, γ w = spec133 γ₀ w := fun w ↦ hAt.1 w w.isLt
  have hγ_17_91 : ∀ w : Wire 133, 17 ≤ w.val → w.val < 92 → γ w = 0 := fun w hlo hhi ↦ by
    rw [hγ_spec w, spec133_of_lt_92 γ₀ w hhi]
    exact hγ₀ w hlo
  obtain ⟨γ1, hFwd1, hVal1, hunary1, hOther1⟩ :=
    DiagCtxWG.wStateTreeCohGate1_step 5 wHas addrLo outLo qEnc shFast_hdLo body1 γ
      (fun k ↦ hγ_17_91 _ (by dsimp [outLo]; omega) (by dsimp [outLo]; have := k.isLt; omega))
      (hγ_17_91 qEnc (by decide) (by decide))
  have hγ1_ge81 : ∀ w : Wire 133, 81 ≤ w.val → γ1 w = γ w := fun w hw ↦
    hOther1 w fun k ↦ wire_ne_of_gt (by dsimp [outLo]; have := k.isLt; omega)
  have hγ1_lt17 : ∀ w : Wire 133, w.val < 17 → γ1 w = γ w := fun w hw ↦
    hOther1 w fun k ↦ wire_ne_of_lt (by dsimp [outLo]; omega)
  obtain ⟨γ2, hFwd2, hVal2, hunary2, hOther2⟩ :=
    DiagCtxWG.wStateTreeCohGate1_step 1 wHas addrHi outHi qEnc shFast_hdHi body2 γ1
      (fun k ↦ (hγ1_ge81 _ (by dsimp [outHi]; omega)).trans
        (hγ_17_91 _ (by dsimp [outHi]; omega) (by dsimp [outHi]; have := k.isLt; omega)))
      ((hγ1_ge81 qEnc (by decide)).trans (hγ_17_91 qEnc (by decide) (by decide)))
  refine ⟨hVal1 (hVal2 trivial), ?_⟩
  let γ3 := cliffSlot0Toggle133.eval γ2
  have hFwd : ctxShiftedTreesFast133.fwdBits γ = γ3 := hFwd1.trans hFwd2
  rw [hFwd]
  let c1 := γ₀ ⟨0, by decide⟩
  let a : Fin 8 → ZMod 2 := fun i ↦ γ₀ ⟨1 + i.val, by omega⟩
  let b : Fin 8 → ZMod 2 := fun i ↦ γ₀ ⟨9 + i.val, by omega⟩
  let wVec := pureW b
  have hwEqFast : pureWFast b = wVec := pureWFast_eq_pureW b
  have hγ3_lt17 : ∀ w : Wire 133, w.val < 17 → γ3 w = γ₀ w := fun w hw ↦ by
    dsimp only [γ3]
    rw [cliffSlot0Toggle133_eval_apply,
        ite_eq_right (wire_ne_of_lt (by dsimp; omega)),
        ite_eq_right (wire_ne_of_lt (by dsimp; omega)),
        ite_eq_right (wire_ne_of_lt (by dsimp; omega)),
        hOther2 w fun k ↦ wire_ne_of_lt (by dsimp [outHi]; omega),
        hγ1_lt17 w hw, hγ_spec w, spec133_of_lt_92 γ₀ w (by omega)]
  have hsEq : bitsVal (pureShiftedIdx8 (γ3 ⟨0, by decide⟩)
      (fun i ↦ γ3 ⟨1 + i.val, by omega⟩) (fun i ↦ γ3 ⟨9 + i.val, by omega⟩)) =
      bitsVal (pureShiftedIdx8 c1 a b) := by
    have h0 : γ3 ⟨0, by decide⟩ = c1 := hγ3_lt17 _ (by decide)
    have ha : (fun i : Fin 8 ↦ γ3 ⟨1 + i.val, by omega⟩) = a :=
      funext fun i ↦ hγ3_lt17 _ (by dsimp; omega)
    have hb : (fun i : Fin 8 ↦ γ3 ⟨9 + i.val, by omega⟩) = b :=
      funext fun i ↦ hγ3_lt17 _ (by dsimp; omega)
    rw [h0, ha, hb]
  have hHas1 : γ1 wHas = γ wHas := hγ1_ge81 wHas (by decide)
  have hHas2 : γ2 wHas = γ wHas :=
    (hOther2 wHas fun k ↦ wire_ne_of_gt (by dsimp [wHas, outHi]; have := k.isLt; omega)).trans
      hHas1
  have hwLo : (fun j : Fin 6 ↦ γ (addrLo j)) = fun j : Fin 6 ↦ wVec ⟨j.val, by omega⟩ := by
    funext j
    rw [hγ_spec (addrLo j)]
    have hjEq : spec133 γ₀ (addrLo j) = pureWFast b ⟨j.val, by omega⟩ := by
      fin_cases j <;> rfl
    rw [hjEq, hwEqFast]
  have hwHi : (fun j : Fin 2 ↦ γ1 (addrHi j)) = fun j : Fin 2 ↦ wVec ⟨6 + j.val, by omega⟩ := by
    funext j
    rw [hγ1_ge81 (addrHi j) (by dsimp [addrHi]; omega), hγ_spec (addrHi j)]
    have hjEq : spec133 γ₀ (addrHi j) = pureWFast b ⟨6 + j.val, by omega⟩ := by
      fin_cases j <;> rfl
    rw [hjEq, hwEqFast]
  have hShiftEq : pureShiftedIdx8 c1 a b = fun k ↦ γ wHas * wVec k := by
    funext k
    rw [hγ_spec wHas]
    have h132 : spec133 γ₀ wHas = (c1 + 1) * (pureWFast b 0 + a 0 + 1) *
        (pureWFast b 1 + a 1 + 1) * (pureWFast b 2 + a 2 + 1) * (pureWFast b 3 + a 3 + 1) *
        (pureWFast b 4 + a 4 + 1) * (pureWFast b 5 + a 5 + 1) * (pureWFast b 6 + a 6 + 1) *
        (pureWFast b 7 + a 7 + 1) + 1 := rfl
    rw [h132, hwEqFast]
    rfl
  have hZero86 : ∀ (t : ℕ) (ht : t < 6), γ3 ⟨86 + t, by omega⟩ = 0 := fun t ht ↦ by
    dsimp only [γ3]
    rw [cliffSlot0Toggle133_eval_apply,
        ite_eq_right (wire_ne_of_gt (by dsimp; omega)),
        ite_eq_right (wire_ne_of_gt (by dsimp; omega)),
        ite_eq_right (wire_ne_of_lt (by dsimp; omega)),
        hOther2 ⟨86 + t, by omega⟩ fun k ↦ wire_ne_of_gt (by dsimp [outHi]; have := k.isLt; omega),
        hγ1_ge81 ⟨86 + t, by omega⟩ (by dsimp; omega)]
    exact hγ_17_91 ⟨86 + t, by omega⟩ (by dsimp; omega) (by dsimp; omega)
  dsimp only [InvShifted64x4Fast]
  rw [hsEq]
  rcases bit_cases (γ wHas) with hHas0 | hHas1Bit
  · have hS0 : bitsVal (pureShiftedIdx8 c1 a b) = 0 := by
      have hFun0 : pureShiftedIdx8 c1 a b = fun _ ↦ 0 := by
        rw [hShiftEq, hHas0]; funext _; simp
      rw [hFun0]; rfl
    rw [hS0]
    have hMod0 : 0 % 64 = 0 := rfl
    have hDiv0 : 0 / 64 = 0 := rfl
    rw [hMod0, hDiv0]
    refine ⟨fun l hl ↦ ?_, fun h hh ↦ ?_, hZero86⟩
    · have hγ2_lo : γ2 ⟨17 + l, by omega⟩ = 0 := by
        rw [hOther2 ⟨17 + l, by omega⟩ fun k ↦ wire_ne_of_lt (by dsimp [outHi]; omega)]
        have h1 := hunary1 ⟨l, hl⟩
        dsimp only [outLo] at h1
        rw [h1, hHas0, ite_self]
      dsimp only [γ3]
      rw [cliffSlot0Toggle133_eval_apply,
          ite_eq_right (wire_ne_of_lt (by dsimp; omega))]
      by_cases hl0 : l = 0
      · subst hl0
        have hw17 : (⟨17 + 0, by omega⟩ : Wire 133) = ⟨17, by decide⟩ := Fin.ext rfl
        rw [ite_eq_left hw17, ite_eq_left rfl, ← hw17, hγ2_lo, hHas2, hHas0]
        rfl
      · have hw17 : (⟨17 + l, by omega⟩ : Wire 133) ≠ ⟨17, by decide⟩ :=
          wire_ne_of_gt (by dsimp; omega)
        rw [ite_eq_right hw17, ite_eq_right (wire_ne_of_lt (by dsimp; omega)),
            ite_eq_right hl0, hγ2_lo]
    · have hγ2_hi : γ2 ⟨81 + h, by omega⟩ = 0 := by
        have h2 := hunary2 ⟨h, hh⟩
        dsimp only [outHi] at h2
        rw [h2, hHas1, hHas0, ite_self]
      dsimp only [γ3]
      rw [cliffSlot0Toggle133_eval_apply]
      by_cases hh0 : h = 0
      · subst hh0
        have hw81 : (⟨81 + 0, by omega⟩ : Wire 133) = ⟨81, by decide⟩ := Fin.ext rfl
        rw [ite_eq_left hw81, ite_eq_left rfl, ← hw81, hγ2_hi, hHas2, hHas0]
        rfl
      · have hw81 : (⟨81 + h, by omega⟩ : Wire 133) ≠ ⟨81, by decide⟩ :=
          wire_ne_of_gt (by dsimp; omega)
        have hw17 : (⟨81 + h, by omega⟩ : Wire 133) ≠ ⟨17, by decide⟩ :=
          wire_ne_of_gt (by dsimp; omega)
        rw [ite_eq_right hw81, ite_eq_right hw17, ite_eq_right (wire_ne_of_lt (by dsimp; omega)),
            ite_eq_right hh0, hγ2_hi]
  · have hEqBit0 : γ2 ⟨132, by decide⟩ + 1 = 0 := by
      change γ2 wHas + 1 = 0
      rw [hHas2, hHas1Bit]; rfl
    have hγ3_eq_γ2 : ∀ w : Wire 133, w ≠ wHas → γ3 w = γ2 w := fun w hw ↦ by
      dsimp only [γ3]
      rw [cliffSlot0Toggle133_eval_apply, hEqBit0, add_zero, add_zero]
      by_cases h81 : w = ⟨81, by decide⟩
      · subst h81; simp
      · rw [ite_eq_right h81]
        by_cases h17 : w = ⟨17, by decide⟩
        · subst h17; simp
        · rw [ite_eq_right h17, ite_eq_right hw]
    have hSW : pureShiftedIdx8 c1 a b = wVec := by
      rw [hShiftEq, hHas1Bit]; funext k; exact one_mul (wVec k)
    rw [hSW]
    have hSplit := bitsVal_split_6_2 wVec
    let loVal := bitsVal (fun j : Fin 6 ↦ wVec ⟨j.val, by omega⟩)
    let hiVal := bitsVal (fun j : Fin 2 ↦ wVec ⟨6 + j.val, by omega⟩)
    have hlo_lt : loVal < 64 := bitsVal_lt_two_pow _
    have hsMod : bitsVal wVec % 64 = loVal := by
      rw [hSplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo_lt]
    have hsDiv : bitsVal wVec / 64 = hiVal := by
      rw [hSplit, Nat.add_mul_div_left _ _ (by decide : 0 < 64),
          Nat.div_eq_of_lt hlo_lt, zero_add]
    rw [hsMod, hsDiv]
    refine ⟨fun l hl ↦ ?_, fun h hh ↦ ?_, hZero86⟩
    · rw [hγ3_eq_γ2 ⟨17 + l, by omega⟩ (wire_ne_of_lt (by dsimp [wHas]; omega)),
          hOther2 ⟨17 + l, by omega⟩ fun k ↦ wire_ne_of_lt (by dsimp [outHi]; omega)]
      have h1 := hunary1 ⟨l, hl⟩
      dsimp only [outLo] at h1
      rw [h1, hwLo, hHas1Bit]
    · rw [hγ3_eq_γ2 ⟨81 + h, by omega⟩ (wire_ne_of_lt (by dsimp [wHas]; omega))]
      have h2 := hunary2 ⟨h, hh⟩
      dsimp only [outHi] at h2
      rw [h2, hwHi, hHas1, hHas1Bit]
/-- Contiguous `133`-wire `64 × 4` zero-gated W-state context for `shiftedPartnerSlotFast`
(`19` ANDs = `76 T` + `138 T` + `10 T` = `224 T`, `116 ≤ mScr`). -/
def ctxShiftedPartnerFast : DiagCtxWG 133 :=
  ctxAnd133 92 (by decide) ⟨9, by decide⟩ ⟨10, by decide⟩ (by decide) (by decide) (by decide) <|
  ctxXor133 93 (by decide) ⟨10, by decide⟩ ⟨9, by decide⟩ (by decide) (by decide) <|
  ctxNot133 94 (by decide) ⟨11, by decide⟩ (by decide) <|
  ctxNot133 95 (by decide) ⟨14, by decide⟩ (by decide) <|
  ctxXnor133 96 (by decide) ⟨92, by decide⟩ ⟨93, by decide⟩ (by decide) (by decide) <|
  ctxNand133 97 (by decide) ⟨96, by decide⟩ ⟨94, by decide⟩ (by decide) (by decide) (by decide) <|
  ctxAnd133 98 (by decide) ⟨12, by decide⟩ ⟨13, by decide⟩ (by decide) (by decide) (by decide) <|
  ctxNand133 99 (by decide) ⟨98, by decide⟩ ⟨97, by decide⟩ (by decide) (by decide) (by decide) <|
  ctxNand133 100 (by decide) ⟨95, by decide⟩ ⟨99, by decide⟩ (by decide) (by decide) (by decide) <|
  ctxAnd133 101 (by decide) ⟨92, by decide⟩ ⟨11, by decide⟩ (by decide) (by decide) (by decide) <|
  ctxAnd133 102 (by decide) ⟨101, by decide⟩ ⟨12, by decide⟩ (by decide) (by decide) (by decide) <|
  ctxAnd133 103 (by decide) ⟨102, by decide⟩ ⟨13, by decide⟩ (by decide) (by decide) (by decide) <|
  ctxAnd133 104 (by decide) ⟨103, by decide⟩ ⟨14, by decide⟩ (by decide) (by decide) (by decide) <|
  ctxAnd133 105 (by decide) ⟨16, by decide⟩ ⟨100, by decide⟩ (by decide) (by decide) (by decide) <|
  ctxXor133 106 (by decide) ⟨105, by decide⟩ ⟨104, by decide⟩ (by decide) (by decide) <|
  ctxAnd133 107 (by decide) ⟨15, by decide⟩ ⟨106, by decide⟩ (by decide) (by decide) (by decide) <|
  ctxNot133 108 (by decide) ⟨9, by decide⟩ (by decide) <|
  ctxXor133 109 (by decide) ⟨10, by decide⟩ ⟨9, by decide⟩ (by decide) (by decide) <|
  ctxXor133 110 (by decide) ⟨11, by decide⟩ ⟨92, by decide⟩ (by decide) (by decide) <|
  ctxXor133 111 (by decide) ⟨12, by decide⟩ ⟨101, by decide⟩ (by decide) (by decide) <|
  ctxXor133 112 (by decide) ⟨13, by decide⟩ ⟨102, by decide⟩ (by decide) (by decide) <|
  ctxXor133 113 (by decide) ⟨14, by decide⟩ ⟨103, by decide⟩ (by decide) (by decide) <|
  ctxXor133 114 (by decide) ⟨15, by decide⟩ ⟨104, by decide⟩ (by decide) (by decide) <|
  ctxXor133 115 (by decide) ⟨16, by decide⟩ ⟨107, by decide⟩ (by decide) (by decide) <|
  ctxNot133 116 (by decide) ⟨0, by decide⟩ (by decide) <|
  ctxXnor133 117 (by decide) ⟨108, by decide⟩ ⟨1, by decide⟩ (by decide) (by decide) <|
  ctxXnor133 118 (by decide) ⟨109, by decide⟩ ⟨2, by decide⟩ (by decide) (by decide) <|
  ctxXnor133 119 (by decide) ⟨110, by decide⟩ ⟨3, by decide⟩ (by decide) (by decide) <|
  ctxXnor133 120 (by decide) ⟨111, by decide⟩ ⟨4, by decide⟩ (by decide) (by decide) <|
  ctxXnor133 121 (by decide) ⟨112, by decide⟩ ⟨5, by decide⟩ (by decide) (by decide) <|
  ctxXnor133 122 (by decide) ⟨113, by decide⟩ ⟨6, by decide⟩ (by decide) (by decide) <|
  ctxXnor133 123 (by decide) ⟨114, by decide⟩ ⟨7, by decide⟩ (by decide) (by decide) <|
  ctxXnor133 124 (by decide) ⟨115, by decide⟩ ⟨8, by decide⟩ (by decide) (by decide) <|
  ctxAnd133 125 (by decide) ⟨116, by decide⟩ ⟨117, by decide⟩
    (by decide) (by decide) (by decide) <|
  ctxAnd133 126 (by decide) ⟨125, by decide⟩ ⟨118, by decide⟩
    (by decide) (by decide) (by decide) <|
  ctxAnd133 127 (by decide) ⟨126, by decide⟩ ⟨119, by decide⟩
    (by decide) (by decide) (by decide) <|
  ctxAnd133 128 (by decide) ⟨127, by decide⟩ ⟨120, by decide⟩
    (by decide) (by decide) (by decide) <|
  ctxAnd133 129 (by decide) ⟨128, by decide⟩ ⟨121, by decide⟩
    (by decide) (by decide) (by decide) <|
  ctxAnd133 130 (by decide) ⟨129, by decide⟩ ⟨122, by decide⟩
    (by decide) (by decide) (by decide) <|
  ctxAnd133 131 (by decide) ⟨130, by decide⟩ ⟨123, by decide⟩
    (by decide) (by decide) (by decide) <|
  ctxNand133 132 (by decide) ⟨131, by decide⟩ ⟨124, by decide⟩
    (by decide) (by decide) (by decide) <|
  ctxShiftedTreesFast133
theorem ctxShiftedPartnerFast_countT : ctxShiftedPartnerFast.countT = 224 := rfl
theorem wa133_not {m : ℕ} {hm : m < 133} {src : Wire 133} {hs : src.val < m} {K : DiagCtxWG 133}
    (hm17 : 17 ≤ m) (hK : DiagCtxWGWritesAbove 17 K) :
    DiagCtxWGWritesAbove 17 (ctxNot133 m hm src hs K) := ⟨⟨hm17, hm17⟩, hK⟩
theorem wa133_xor {m : ℕ} {hm : m < 133} {s₁ s₂ : Wire 133} {h₁ : s₁.val < m} {h₂ : s₂.val < m}
    {K : DiagCtxWG 133} (hm17 : 17 ≤ m) (hK : DiagCtxWGWritesAbove 17 K) :
    DiagCtxWGWritesAbove 17 (ctxXor133 m hm s₁ s₂ h₁ h₂ K) := ⟨⟨hm17, hm17⟩, hK⟩
theorem wa133_xnor {m : ℕ} {hm : m < 133} {s₁ s₂ : Wire 133} {h₁ : s₁.val < m} {h₂ : s₂.val < m}
    {K : DiagCtxWG 133} (hm17 : 17 ≤ m) (hK : DiagCtxWGWritesAbove 17 K) :
    DiagCtxWGWritesAbove 17 (ctxXnor133 m hm s₁ s₂ h₁ h₂ K) := ⟨⟨hm17, hm17, hm17⟩, hK⟩
theorem wa133_and {m : ℕ} {hm : m < 133} {c₁ c₂ : Wire 133} {h₁₂ : c₁ ≠ c₂} {h₁ : c₁.val < m}
    {h₂ : c₂.val < m} {K : DiagCtxWG 133} (hm17 : 17 ≤ m) (hK : DiagCtxWGWritesAbove 17 K) :
    DiagCtxWGWritesAbove 17 (ctxAnd133 m hm c₁ c₂ h₁₂ h₁ h₂ K) := ⟨hm17, hK⟩
theorem wa133_nand {m : ℕ} {hm : m < 133} {c₁ c₂ : Wire 133} {h₁₂ : c₁ ≠ c₂} {h₁ : c₁.val < m}
    {h₂ : c₂.val < m} {K : DiagCtxWG 133} (hm17 : 17 ≤ m) (hK : DiagCtxWGWritesAbove 17 K) :
    DiagCtxWGWritesAbove 17 (ctxNand133 m hm c₁ c₂ h₁₂ h₁ h₂ K) := ⟨hm17, hm17, hK⟩
theorem ctxShiftedPartnerFast_writesAbove : DiagCtxWGWritesAbove 17 ctxShiftedPartnerFast := by
  dsimp only [ctxShiftedPartnerFast]
  repeat first
    | refine wa133_not (by decide) ?_
    | refine wa133_xor (by decide) ?_
    | refine wa133_xnor (by decide) ?_
    | refine wa133_and (by decide) ?_
    | refine wa133_nand (by decide) ?_
  exact ⟨fun l ↦ by dsimp; omega, fun l ↦ by dsimp; omega,
    ⟨by dsimp [CliffWritesAbove]; decide, by dsimp [CliffWritesAbove]; decide,
      by dsimp [CliffWritesAbove]; decide⟩,
    trivial⟩
theorem ctxShiftedPartnerFast_spec (γ : BitAssignment 133) (hγ : CleanScr116 γ) :
    ctxShiftedPartnerFast.ValidAt γ ∧
      InvShifted64x4Fast (ctxShiftedPartnerFast.fwdBits γ) := by
  have hAt92 : AtStage133 γ 92 γ := ⟨fun w hw ↦ (spec133_of_lt_92 γ w hw).symm,
    fun w hw ↦ hγ w (by omega)⟩
  refine (?_ : RunFrom133 γ 92 ctxShiftedPartnerFast) γ hAt92
  dsimp only [ctxShiftedPartnerFast]
  repeat first
    | apply runFrom133_ctxNot _ _ _ _ rfl
    | apply runFrom133_ctxXor _ _ _ _ _ _ rfl
    | apply runFrom133_ctxXnor _ _ _ _ _ _ rfl
    | apply runFrom133_ctxAnd _ _ _ _ _ _ _ rfl
    | apply runFrom133_ctxNand _ _ _ _ _ _ _ rfl
  exact runFrom_trees_fast γ hγ
/-! ## Section 2D: `116`-Wire Scratch Projector Bridge, `ActPreservesShifted17`, & Parametric
`dWithShiftedPartnerFast` -/
/-- Selector `selDataInAct kData : QRegister kData (kData + 18)` extracting `rData` (`[0 .. kData)`)
from `rData.concat rMeas hDM`. -/
def selDataInAct (kData : ℕ) : QRegister kData (kData + 18) :=
  QRegister.block 0 kData (by omega)
theorem selDataInAct_apply {kData : ℕ} (i : Fin kData) :
    selDataInAct kData i = Fin.castAdd 18 i :=
  Fin.ext (by simp [selDataInAct, QRegister.block])
/-- `17`-wire shifted-index selector lifted inside `kData`. -/
def selShiftedIdx17 {kData : ℕ} (selCore : QRegister posCoreWires kData) : QRegister 17 kData :=
  selCore.compose rShiftedIdx17OfFin
/-- Predicate asserting that unitary `V` on `kData + 18` preserves `selShiftedIdx17 selCore`. -/
def ActPreservesShifted17 {kData : ℕ} (selCore : QRegister posCoreWires kData)
    (V : Unitary (2 ^ (kData + 18))) : Prop := ∀ (xy y : Fin (2 ^ (kData + 18))), V.1 y xy ≠ 0
    → (selShiftedIdx17 selCore).extractIndex ((selDataInAct kData).extractIndex y) =
    (selShiftedIdx17 selCore).extractIndex ((selDataInAct kData).extractIndex xy)
theorem actPreservesShifted17_mul {kData : ℕ} (selCore : QRegister posCoreWires kData)
    {U V : Unitary (2 ^ (kData + 18))} (hU : ActPreservesShifted17 selCore U)
    (hV : ActPreservesShifted17 selCore V) : ActPreservesShifted17 selCore (U * V) := by
  intro xy z hnz
  rw [Submonoid.coe_mul, Matrix.mul_apply] at hnz
  obtain ⟨y, _, hyz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
  exact (hU y z (left_ne_zero_of_mul hyz)).trans (hV xy y (right_ne_zero_of_mul hyz))
/-- Predicate asserting that scratch wires at indices `≥ 116` of `rScr` are initialized to `0`. -/
def Scr116Zero {n mScr : ℕ} (rScr : QRegister mScr n) (β : BitAssignment n) : Prop :=
  ∀ k : Fin mScr, 116 ≤ k.val → β (rScr k) = 0
theorem scr_zero_iff_cleanScr116 {n mScr : ℕ} (hm : 116 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (β : BitAssignment n) : (∀ k : Fin mScr, β (rScr k) = 0)
    ↔ (Scr116Zero rScr β ∧ CleanScr116 (fun idx ↦ β (rComb133 hm rCore rScr hCS idx))) := by
  constructor
  · intro h0
    refine ⟨fun k _ ↦ h0 k, fun idx hge ↦ ?_⟩
    dsimp only
    rw [rComb133_apply_ge hm rCore rScr hCS idx hge]
    exact h0 _
  · rintro ⟨h116, hClean⟩ k
    by_cases hk : 116 ≤ k.val
    · exact h116 k hk
    · have hEq : rScr k = rComb133 hm rCore rScr hCS ⟨17 + k.val, by omega⟩ := by
        rw [rComb133_apply_ge hm rCore rScr hCS ⟨17 + k.val, by omega⟩ (by dsimp; omega)]
        exact congrArg rScr.wires (Fin.ext (by dsimp; omega))
      rw [hEq]
      exact hClean ⟨17 + k.val, by omega⟩ (by dsimp; omega)
theorem invHoleShifted218_of_invShifted64x4Fast {n mScr : ℕ} (hm : 116 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (β : BitAssignment n)
    (hInv : InvShifted64x4Fast (fun idx ↦ β (rComb133 hm rCore rScr hCS idx))) :
    InvHoleShifted218 (by omega : 75 ≤ mScr) rCore rScr β := by
  obtain ⟨hLo, hHi, hZero⟩ := hInv
  have h0 : β (rComb133 hm rCore rScr hCS ⟨0, by decide⟩) =
      β (rCore (wSlot1Core (QRegExt.ofFin posCoreWires))) := by
    rw [rComb133_apply_lt hm rCore rScr hCS ⟨0, by decide⟩ (by decide)]
    dsimp only [rShiftedIdx17Core, QRegister.compose_apply]
    rw [rShiftedIdx17OfFin_zero]
  have hA : (fun i : Fin 8 ↦ β (rComb133 hm rCore rScr hCS ⟨1 + i.val, by omega⟩)) =
      fun i ↦ β (rCore (rAnchorIdx (QRegExt.ofFin posCoreWires) i)) :=
    funext fun i ↦ by
      rw [rComb133_apply_lt hm rCore rScr hCS ⟨1 + i.val, by omega⟩ (by dsimp; omega)]
      dsimp only [rShiftedIdx17Core, QRegister.compose_apply]
      rw [rShiftedIdx17OfFin_anc i]
  have hB : (fun i : Fin 8 ↦ β (rComb133 hm rCore rScr hCS ⟨9 + i.val, by omega⟩)) =
      fun i ↦ β (rCore (rPartnerIdx (QRegExt.ofFin posCoreWires) i)) :=
    funext fun i ↦ by
      rw [rComb133_apply_lt hm rCore rScr hCS ⟨9 + i.val, by omega⟩ (by dsimp; omega)]
      dsimp only [rShiftedIdx17Core, QRegister.compose_apply]
      rw [rShiftedIdx17OfFin_part i]
  have hsEq : bitsVal (pureShiftedIdx8
      (β (rComb133 hm rCore rScr hCS ⟨0, by decide⟩))
      (fun i ↦ β (rComb133 hm rCore rScr hCS ⟨1 + i.val, by omega⟩))
      (fun i ↦ β (rComb133 hm rCore rScr hCS ⟨9 + i.val, by omega⟩))) =
      (shiftedPartnerSlotFast (fun w ↦ β (rCore w))).val := by
    rw [h0, hA, hB]
    exact pureShiftedIdx8_bitsVal_eq (fun w ↦ β (rCore w))
  simp only [hsEq] at hLo hHi
  refine ⟨fun l ↦ ?_, fun h ↦ ?_, ?_, fun r ↦ ?_, ?_⟩
  · have hEq : rScr ⟨l.val, by omega⟩ = rComb133 hm rCore rScr hCS ⟨17 + l.val, by omega⟩ := by
      rw [rComb133_apply_ge hm rCore rScr hCS ⟨17 + l.val, by omega⟩ (by dsimp; omega)]
      exact congrArg rScr.wires (Fin.ext (by dsimp; omega))
    rw [hEq]; exact hLo l.val l.isLt
  · have hEq : rScr ⟨64 + h.val, by omega⟩ =
        rComb133 hm rCore rScr hCS ⟨81 + h.val, by omega⟩ := by
      rw [rComb133_apply_ge hm rCore rScr hCS ⟨81 + h.val, by omega⟩ (by dsimp; omega)]
      exact congrArg rScr.wires (Fin.ext (by dsimp; omega))
    rw [hEq]; exact hHi h.val h.isLt
  · have hEq : rScr ⟨69, by omega⟩ = rComb133 hm rCore rScr hCS ⟨86 + 0, by omega⟩ := by
      rw [rComb133_apply_ge hm rCore rScr hCS ⟨86, by decide⟩ (by decide)]
      exact congrArg rScr.wires (Fin.ext rfl)
    rw [hEq]; exact hZero 0 (by decide)
  · have hEq : p2dSubReg rScr 70 4 (by omega) r =
        rComb133 hm rCore rScr hCS ⟨86 + (1 + r.val), by omega⟩ := by
      rw [rComb133_apply_ge hm rCore rScr hCS ⟨86 + (1 + r.val), by omega⟩ (by dsimp; omega)]
      exact congrArg rScr.wires (Fin.ext (by dsimp [p2dSubReg]; omega))
    rw [hEq]; exact hZero (1 + r.val) (by omega)
  · have hEq : rScr ⟨74, by omega⟩ = rComb133 hm rCore rScr hCS ⟨86 + 5, by omega⟩ := by
      rw [rComb133_apply_ge hm rCore rScr hCS ⟨91, by decide⟩ (by decide)]
      exact congrArg rScr.wires (Fin.ext rfl)
    rw [hEq]; exact hZero 5 (by decide)
theorem actPreservesShifted17_to_comb133Pres {n kData mScr : ℕ} (hm : 116 ≤ mScr)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rMeas : QRegister 18 n) (rScr : QRegister mScr n)
    (hDM : rData.DisjointWires rMeas)
    (hDS : rData.DisjointWires rScr)
    (hMS : rMeas.DisjointWires rScr)
    {V : Unitary (2 ^ (kData + 18))} (hV : ActPreservesShifted17 selCore V) :
    let rCore := rData.compose selCore
    let rAct := rData.concat rMeas hDM
    let hCS : rCore.DisjointWires rScr := hDS.compose_left selCore
    let rComb := rComb133 hm rCore rScr hCS
    (∀ idx : Wire 133, 17 ≤ idx.val → rComb idx ∉ Set.range rAct.wires) ∧
    (∀ (idx : Wire 133) (g : Fin (2 ^ n)) (y : Fin (2 ^ (kData + 18))),
      V.1 y (rAct.extractIndex g) ≠ 0 →
      basisBits n (rAct.replaceIndex g y) (rComb idx) = basisBits n g (rComb idx)) := by
  intro rCore rAct hCS rComb
  have hScrNotAct : ∀ k : Fin mScr, rScr k ∉ Set.range rAct.wires :=
    fun k ⟨idx, hidx⟩ ↦ (disjointWires_concat_left hDM hDS hMS).ne idx k hidx
  have hOut : ∀ idx : Wire 133, 17 ≤ idx.val → rComb idx ∉ Set.range rAct.wires := by
    intro idx hge
    rw [rComb133_apply_ge hm rCore rScr hCS idx hge]
    exact hScrNotAct _
  refine ⟨hOut, fun idx g y hnz ↦ ?_⟩
  by_cases hge : 17 ≤ idx.val
  · exact QRegister.basisBits_replaceIndex_of_not_mem rAct g y _ (hOut idx hge)
  · have hlt : idx.val < 17 := by omega
    rw [rComb133_apply_lt hm rCore rScr hCS idx hlt]
    let i : Fin 17 := ⟨idx.val, hlt⟩
    let selS : QRegister 17 (kData + 18) :=
      (selDataInAct kData).compose (selShiftedIdx17 selCore)
    have hwEq : rShiftedIdx17Core rCore i = rAct (selS i) := by
      dsimp only [rAct, selS, QRegister.compose_apply]
      rw [selDataInAct_apply, QRegister.concat_apply_left]
      rfl
    rw [hwEq]
    change basisBits n (rAct.replaceIndex g y) (rAct.wires (selS i)) =
      basisBits n g (rAct.wires (selS i))
    rw [QRegister.basisBits_replaceIndex_apply,
        ← QRegister.basisBits_extractIndex rAct g (selS i)]
    have hexSelS : ∀ xy : Fin (2 ^ (kData + 18)), basisBits (kData + 18) xy (selS i) =
        basisBits 17 ((selShiftedIdx17 selCore).extractIndex ((selDataInAct
        kData).extractIndex xy)) i :=
      fun xy ↦ by
        dsimp only [selS]
        rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
            QRegister.compose_apply]
    rw [hexSelS y, hexSelS (rAct.extractIndex g), hV (rAct.extractIndex g) y hnz]
theorem p2d_ketPredProj_mul_ketPredProj_local {n : ℕ} (S₁ S₂ : BitAssignment n → Prop) :
    p2d_ketPredProj S₁ * p2d_ketPredProj S₂ = p2d_ketPredProj (fun β ↦ S₁ β ∧ S₂ β) := by
  ext i j
  dsimp only [p2d_ketPredProj]
  rw [Matrix.diagonal_mul_diagonal]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.diagonal_apply_eq]
    by_cases h1 : S₁ (basisBits n i) <;> by_cases h2 : S₂ (basisBits n i) <;> simp [h1, h2]
  · simp [Matrix.diagonal_apply_ne _ hij]
attribute [irreducible]
  cCohShiftPre wCohShiftLevel wCohShiftLevels wStateComputeCohGate1 wStateUncomputeCohGate1
end Part2_ShiftedPartnerFastBoothOpt
end BoothOpt_StageBPartnerCoreShave
end
end BoothOpt_StageBPartnerCoreShave

noncomputable section BoothOpt_P4_10a_TwoLoadHeldRowCore

section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option exponentiation.threshold 256
namespace BoothOpt_P4_10_TwoLoadHeldRowTrueSwap
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroTwoPowP410 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Real HermitianMat
open SpecsAux.SpecMirror
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open Circuit hiding TOFF T
open PrimitiveGate (TOFF T)
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open MeasureBranchHadamardSem (ket bitSign sqrtHalf bit_cases
  eval_seq_mulVec ket_H ket_X ket_CNOT ket_TOFF matrix_ext_ket ket_projector_zero ket_projector_one
  sqrtHalf_mul_sqrtHalf)
open CoinDispatchedBarrel288.Internal (CliffProg)
open PosSlots24BranchConcrete
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open PosSlots24PartnerMuxZeroT123 hiding ite_pos ite_neg dite_pos dite_neg
open PosSlots24Barrel3Pass
open AnchorSwap0Split133
open MultiBankWStateRouter
open ParticleOneHotWState
open BoothOpt_StageBPartnerCoreShave (DiagCtxWG
  DiagCtxWGWritesAbove wStateComputeCohGate1 wStateUncomputeCohGate1 count_wStateComputeCohGate1
  count_wStateUncomputeCohGate1 subspaceStep_wStateComputeCohGate1
  subspaceStep_wStateUncomputeCohGate1 wRouterDisj_onRegister InvHoleShifted218 rShiftedIdx17OfFin
  rShiftedIdx17OfFin_zero rShiftedIdx17OfFin_anc rShiftedIdx17OfFin_part selShiftedIdx17
  p2d_ketPredProj_mul_ketPredProj_local rElecSlot_ofFin_val_local shiftedPartnerSlotFast_congr
  shiftedPartnerSlotFast_congr_outside DiagCtxWGCommutesWith diagCtxWGWritesAbove_to_commutesWith)
/-- Re-export of `BoothOpt_StageBPartnerCoreShave.shiftedPartnerSlotFast`. -/
abbrev shiftedPartnerSlotFast :=
  BoothOpt_StageBPartnerCoreShave.shiftedPartnerSlotFast
/-- Re-export of `BoothOpt_StageBPartnerCoreShave.ActPreservesShifted17`. -/
abbrev ActPreservesShifted17 :=
  @BoothOpt_StageBPartnerCoreShave.ActPreservesShifted17
-- ============================================================================
-- Section 1: `SubspaceStep` Combinators & `DiagCtxWG` (`toDynWGLocal`, `uFwdWG`)
-- ============================================================================
theorem supportedOn_mul_right {n : ℕ} {Pred : BitAssignment n → Prop}
    {R : Operator (2 ^ n)} (hSupp : SupportedOn Pred R) (A : Operator (2 ^ n)) :
    SupportedOn Pred (R * A) := fun X Y hXY ↦ by
  rw [← Matrix.mul_assoc, hSupp X Y hXY, Matrix.mul_assoc]
theorem supportedOn_ketPredProj {n : ℕ} (Pred S : BitAssignment n → Prop)
    (hImp : ∀ β, S β → Pred β) :
    SupportedOn Pred (p2d_ketPredProj S) := fun X Y hXY ↦ by
  classical
  apply matrix_ext_ket; intro β
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, p2d_ketPredProj_mul_ket]
  by_cases hs : S β
  · rw [ite_eq_left hs]; exact hXY β (hImp β hs)
  · rw [ite_eq_right hs, Matrix.mulVec_zero, Matrix.mulVec_zero]
theorem supportedOn_basisOutcomeProjector_zero {n k : ℕ} (r : QRegister k n) :
    SupportedOn (fun β ↦ ∀ i : Fin k, β (r i) = 0) (r.basisOutcomeProjector 0) := by
  rw [p2d_basisOutcomeProjector_zero_eq_ketPredProj]
  exact supportedOn_ketPredProj _ _ fun _ h ↦ h
theorem supportedOn_unitary_mul {n : ℕ} {P Q : BitAssignment n → Prop}
    (U : Operator (2 ^ n)) (f : BitAssignment n → BitAssignment n)
    (hU : ∀ β, U.mulVec (ket β) = ket (f β))
    (hImp : ∀ β, P β → Q (f β))
    {R : Operator (2 ^ n)} (hSupp : SupportedOn P R) :
    SupportedOn Q (U * R) := fun A B hAB ↦ by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  exact hSupp (A * U) (B * U) fun β hP ↦ by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hU β]
    exact hAB (f β) (hImp β hP)
theorem subspaceStep_seq_measureXReset {Var : Type} [Fintype Var] [DecidableEq Var] {n k : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rOut : QRegister k n) {R₀ R₁ R₂ : Operator (2 ^ n)}
    {dPre : DynamicCircuit Var n} {cont : (Fin k → Bool) → DynamicCircuit Var n}
    (hPre : SubspaceStep R₀ R₁ dPre) (hCont : ∀ f : Fin k → Bool, SubspaceStep
    (DynCircuitExt.xResetKraus rOut f * R₁) ((((√(1 / 2)) ^ k : ℝ) : ℂ) • R₂) (cont f)) :
    SubspaceStep R₀ R₂ (.seq dPre (DynCircuitExt.measureXResetAndBranch v k rOut cont)) := by
  intro M
  choose MCont hCont_wp hCont_eq using fun f ↦ hCont f M
  obtain ⟨MMid, hMid_wp, hMid_mat⟩ :=
    DynCircuitExt.wp_measureXResetAndBranch_const v k rOut cont M MCont hCont_wp
  obtain ⟨M', hPre_wp, hPre_eq⟩ := hPre MMid
  refine ⟨M', ?_, ?_⟩
  · change wp (DynamicCircuit.seq dPre (DynCircuitExt.measureXResetAndBranch v k rOut
      cont)).compile
      (fun _ ↦ M) = fun _ ↦ M'
    rw [DynamicCircuit.compile_seq, wp_qSeq, hMid_wp, hPre_wp]
  · rw [← hPre_eq, hMid_mat, Matrix.mul_sum, Matrix.sum_mul]
    let w : ℝ := (√(1 / 2)) ^ k
    have hstar : star (w : ℂ) = (w : ℂ) := Complex.conj_ofReal w
    have hTerm : ∀ f : Fin k → Bool,
        R₁ᴴ * ((DynCircuitExt.xResetKraus rOut f)ᴴ * (MCont f).1.1 *
          DynCircuitExt.xResetKraus rOut f) * R₁ =
        ((w ^ 2 : ℝ) : ℂ) • (R₂ᴴ * M.1.1 * R₂) := fun f ↦ by
      calc R₁ᴴ * ((DynCircuitExt.xResetKraus rOut f)ᴴ * (MCont f).1.1 *
            DynCircuitExt.xResetKraus rOut f) * R₁
          = (DynCircuitExt.xResetKraus rOut f * R₁)ᴴ * (MCont f).1.1 *
              (DynCircuitExt.xResetKraus rOut f * R₁) := by
              simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = ((w : ℂ) • R₂)ᴴ * M.1.1 * ((w : ℂ) • R₂) := (hCont_eq f).symm
        _ = ((w ^ 2 : ℝ) : ℂ) • (R₂ᴴ * M.1.1 * R₂) := by
              simp only [Matrix.conjTranspose_smul, hstar, Matrix.smul_mul,
                Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
              congr 1; push_cast; ring
    rw [Finset.sum_congr rfl fun f _ ↦ hTerm f, ← Finset.sum_smul]
    have hsum_c : (∑ _f : Fin k → Bool, ((w ^ 2 : ℝ) : ℂ)) = 1 := by
      exact_mod_cast DynCircuitExt.sum_sqrt_half_pow_sq k
    rw [hsum_c, one_smul]
/-- Classical reversible Toffoli-equivalent permutation unitary XORing `c₁ * c₂` onto `anc`. -/
noncomputable def uTempAnd {n : ℕ} (c₁ c₂ anc : Wire n)
    (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc) : Unitary (2 ^ n) :=
  xorWireUnitary anc (fun β ↦ β c₁ * β c₂) (fun β a ↦ by
    rw [Function.update_of_ne h₁a, Function.update_of_ne h₂a])
theorem uTempAnd_mulVec_ket {n : ℕ} (c₁ c₂ anc : Wire n) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (β : BitAssignment n) : (uTempAnd c₁ c₂ anc h₁a h₂a).1.mulVec (ket β) = ket
    (Function.update β anc (β anc + β c₁ * β c₂)) := xorWireUnitary_mulVec_ket _ _ _ β
theorem uTempAnd_eq_toff {n : ℕ} (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc)
    (h₂a : c₂ ≠ anc) : uTempAnd c₁ c₂ anc h₁a h₂a =
    (Circuit.gate TOFF (QRegister.triple c₁ c₂ anc h₁₂ h₁a h₂a)).eval := by
  apply Subtype.ext; apply matrix_ext_ket; intro β
  rw [uTempAnd_mulVec_ket]
  exact (ket_TOFF c₁ c₂ anc h₁₂ h₁a h₂a β).symm
theorem subspaceStep_andCompute {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)]
    (c₁ c₂ anc : Wire n) (_h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (R_in : Operator (2 ^ n)) (hSupp : SupportedOn (fun β ↦ β anc = 0) R_in) :
    SubspaceStep (Var := Var) R_in ((uTempAnd c₁ c₂ anc h₁a h₂a).1 * R_in)
      (DynamicCircuit.andCompute c₁ c₂ anc h₁a h₂a) :=
  subspaceStep_congr_out
    (subspaceStep_of_circuit (Var := Var) R_in (Circuit.andCompute c₁ c₂ anc h₁a h₂a))
    (hSupp _ _ fun β h0 ↦ by
      rw [ZeroAncillaUSP.ket_andCompute_of_zero c₁ c₂ anc h₁a h₂a β h0,
          uTempAnd_mulVec_ket c₁ c₂ anc h₁a h₂a β, h0, zero_add])
theorem cHadCnotHad_mulVec_ket {n : ℕ} (c₁ c₂ : Wire n) (h₁₂ : c₁ ≠ c₂) (β : BitAssignment n) :
    (Circuit.H c₂ ;;ᶜ Circuit.CNOT c₁ c₂ h₁₂ ;;ᶜ Circuit.H c₂).eval.1.mulVec (ket β) =
      bitSign (β c₁ * β c₂) • ket β := by
  simp only [eval_seq_mulVec, ket_H, ket_CNOT, Matrix.mulVec_smul, Matrix.mulVec_add,
    Function.update_self, Function.update_of_ne h₁₂, Function.update_idem]
  rcases bit_cases (β c₁) with hc0 | hc1 <;> rcases bit_cases (β c₂) with hd0 | hd1
  · simp [hc0, hd0, bitSign, update_eq_self_of_zero hd0, smul_add, smul_smul, sqrtHalf_mul_sqrtHalf]
    module
  · have hup1 : Function.update β c₂ 1 = β := by
      funext w; by_cases hw : w = c₂
      · subst hw; simp [hd1]
      · simp [hw]
    simp [hc0, hd1, bitSign, hup1, smul_add, smul_smul, sqrtHalf_mul_sqrtHalf]
    module
  · simp [hc1, hd0, bitSign, update_eq_self_of_zero hd0, smul_add, smul_smul, sqrtHalf_mul_sqrtHalf]
    module
  · have hup1 : Function.update β c₂ 1 = β := by
      funext w; by_cases hw : w = c₂
      · subst hw; simp [hd1]
      · simp [hw]
    have h11 : (1 : ZMod 2) + 1 = 0 := rfl
    simp [hc1, hd1, h11, bitSign, hup1, smul_add, smul_smul, sqrtHalf_mul_sqrtHalf]
    module
theorem subspaceStep_andUncompute {Var : Type} [Fintype Var] [DecidableEq Var]
    {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (c₁ c₂ anc : Wire n) (h₁₂ : c₁ ≠ c₂) (h₁a : c₁ ≠ anc) (h₂a : c₂ ≠ anc)
    (R_out : Operator (2 ^ n)) (hSupp : SupportedOn (fun β ↦ β anc = 0) R_out) :
    SubspaceStep (Var := Var) ((uTempAnd c₁ c₂ anc h₁a h₂a).1 * R_out) R_out
      (DynamicCircuit.andUncompute v c₁ c₂ anc h₁₂) := by
  let cFix := Circuit.H c₂ ;;ᶜ Circuit.CNOT c₁ c₂ h₁₂ ;;ᶜ Circuit.H c₂
  change SubspaceStep ((uTempAnd c₁ c₂ anc h₁a h₂a).1 * R_out) R_out
    ((DynamicCircuit.circuit (Circuit.H anc)).seq (zResetFixupDyn v anc cFix))
  refine subspaceStep_seq_zResetFixup v anc cFix
    (subspaceStep_of_circuit _ (Circuit.H anc)) ?_ ?_
  · simp only [← Matrix.mul_assoc]
    rw [show sqrtHalf • R_out = (sqrtHalf • (1 : Operator (2 ^ n))) * R_out by
      rw [Matrix.smul_mul, Matrix.one_mul]]
    exact hSupp _ _ fun β h0 ↦ by
      rw[Matrix.smul_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
          ← Matrix.mulVec_mulVec, uTempAnd_mulVec_ket, h0, zero_add, ket_H anc,
          Function.update_self, Function.update_idem, Matrix.mulVec_smul, Matrix.mulVec_add,
          ket_projector_zero, Function.update_self, ite_eq_left rfl, Matrix.mulVec_smul,
          ket_projector_zero, Function.update_self, ite_eq_right one_ne_zero, smul_zero, add_zero,
          update_eq_self_of_zero h0]
  · simp only [← Matrix.mul_assoc]
    rw [show sqrtHalf • R_out = (sqrtHalf • (1 : Operator (2 ^ n))) * R_out by
      rw [Matrix.smul_mul, Matrix.one_mul]]
    exact hSupp _ _ fun β h0 ↦ by
      dsimp only [cFix]
      simp only[Matrix.smul_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, uTempAnd_mulVec_ket,
          h0, zero_add, ket_H anc, Function.update_self, Function.update_idem, Matrix.mulVec_smul,
          Matrix.mulVec_add, ket_projector_one, zero_ne_one, ↓reduceIte, ket_X,
          CharTwo.add_self_eq_zero, update_eq_self_of_zero h0, cHadCnotHad_mulVec_ket c₁ c₂ h₁₂ β,
          smul_smul]
      rcases bit_cases (β c₁ * β c₂) with hp0 | hp1
      · simp [hp0, bitSign]
      · simp [hp1, bitSign]
theorem cliffProg_onRegister_eval {M n : ℕ} (rComb : QRegister M n) :
    ∀ (c : CliffProg M) (β : BitAssignment n),
      (c.onRegister rComb).eval β = p2d_writeReg β rComb (c.eval (fun idx ↦ β (rComb idx)))
  | .nil, β => by
      funext w
      by_cases hw : w ∈ Set.range rComb.wires
      · obtain ⟨i, rfl⟩ := hw; rw [p2d_writeReg_apply_reg]; rfl
      · rw [p2d_writeReg_apply_of_not_mem _ _ _ _ hw]; rfl
  | .x q, β => by
      funext w
      dsimp only [CliffProg.onRegister, CliffProg.eval]
      by_cases hwq : w = rComb q
      · subst hwq; rw [Function.update_self, p2d_writeReg_apply_reg, Function.update_self]
      · rw [Function.update_of_ne hwq]
        by_cases hw : w ∈ Set.range rComb.wires
        · obtain ⟨i, rfl⟩ := hw
          have hiq : i ≠ q := fun h ↦ hwq (congrArg rComb.wires h)
          rw [p2d_writeReg_apply_reg, Function.update_of_ne hiq]
        · rw [p2d_writeReg_apply_of_not_mem _ _ _ _ hw]
  | .cnot c t hne, β => by
      funext w
      dsimp only [CliffProg.onRegister, CliffProg.eval]
      by_cases hwt : w = rComb t
      · subst hwt; rw [Function.update_self, p2d_writeReg_apply_reg, Function.update_self]
      · rw [Function.update_of_ne hwt]
        by_cases hw : w ∈ Set.range rComb.wires
        · obtain ⟨i, rfl⟩ := hw
          have hit : i ≠ t := fun h ↦ hwt (congrArg rComb.wires h)
          rw [p2d_writeReg_apply_reg, Function.update_of_ne hit]
        · rw [p2d_writeReg_apply_of_not_mem _ _ _ _ hw]
  | .seq c₁ c₂, β => by
      dsimp only [CliffProg.onRegister, CliffProg.eval]
      rw [cliffProg_onRegister_eval rComb c₁ β,
          cliffProg_onRegister_eval rComb c₂ (p2d_writeReg β rComb (c₁.eval (fun idx ↦ β (rComb
              idx))))]
      have hRead : (fun idx ↦ p2d_writeReg β rComb (c₁.eval (fun i ↦ β (rComb i))) (rComb idx)) =
          c₁.eval (fun i ↦ β (rComb i)) := funext fun idx ↦ p2d_writeReg_apply_reg _ _ _ idx
      rw [hRead]
      funext w
      by_cases hw : w ∈ Set.range rComb.wires
      · obtain ⟨i, rfl⟩ := hw; rw [p2d_writeReg_apply_reg, p2d_writeReg_apply_reg]
      · rw[p2d_writeReg_apply_of_not_mem _ _ _ _ hw, p2d_writeReg_apply_of_not_mem _ _ _ _ hw,
          p2d_writeReg_apply_of_not_mem _ _ _ _ hw]
theorem p2d_writeReg_update {M n : ℕ} (rComb : QRegister M n) (β : BitAssignment n)
    (q : Wire M) (val : ZMod 2) : Function.update β (rComb q) val = p2d_writeReg β rComb
    (Function.update (fun idx ↦ β (rComb idx)) q val) := by
  funext w
  by_cases hwq : w = rComb q
  · subst hwq; rw [Function.update_self, p2d_writeReg_apply_reg, Function.update_self]
  · rw [Function.update_of_ne hwq]
    by_cases hw : w ∈ Set.range rComb.wires
    · obtain ⟨i, rfl⟩ := hw
      have hiq : i ≠ q := fun h ↦ hwq (congrArg rComb.wires h)
      rw [p2d_writeReg_apply_reg, Function.update_of_ne hiq]
    · rw [p2d_writeReg_apply_of_not_mem _ _ _ _ hw]
theorem p2d_writeReg_writeReg {M n : ℕ} (rComb : QRegister M n) (β : BitAssignment n)
    (γ₁ γ₂ : BitAssignment M) :
    p2d_writeReg (p2d_writeReg β rComb γ₁) rComb γ₂ = p2d_writeReg β rComb γ₂ := by
  funext w
  by_cases hw : w ∈ Set.range rComb.wires
  · obtain ⟨i, rfl⟩ := hw; rw [p2d_writeReg_apply_reg, p2d_writeReg_apply_reg]
  · rw[p2d_writeReg_apply_of_not_mem _ _ _ _ hw, p2d_writeReg_apply_of_not_mem _ _ _ _ hw,
      p2d_writeReg_apply_of_not_mem _ _ _ _ hw]
theorem p2d_writeReg_self {M n : ℕ} (rComb : QRegister M n) (β : BitAssignment n) :
    p2d_writeReg β rComb (fun idx ↦ β (rComb idx)) = β := by
  funext w
  by_cases hw : w ∈ Set.range rComb.wires
  · obtain ⟨i, rfl⟩ := hw; exact p2d_writeReg_apply_reg _ _ _ i
  · exact p2d_writeReg_apply_of_not_mem _ _ _ _ hw
/-- Global forward permutation unitary of `DiagCtxWG M` embedded on `rComb : QRegister M n`. -/
noncomputable def uFwdWG {M n : ℕ} (rComb : QRegister M n) : DiagCtxWG M → Unitary (2 ^ n)
  | .hole => 1
  | .cliffConj c K => uFwdWG rComb K * (c.onRegister rComb).toCircuit.eval
  | .tempAnd c₁ c₂ anc _ h₁a h₂a K =>
      uFwdWG rComb K * uTempAnd (rComb c₁) (rComb c₂) (rComb anc)
        (rComb.wires.injective.ne h₁a) (rComb.wires.injective.ne h₂a)
  | .wStateTree _ wIdx wOut _ hd K =>
      let hdN := wUncondDisjProp_onRegister rComb hd
      uFwdWG rComb K * uOneHotUncond (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l)) hdN.1
  | .wStateTreeCohGate1 _ wHas wIdx wOut _ hd K =>
      let hdN := wRouterDisj_onRegister rComb hd
      uFwdWG rComb K * uOneHotToggle (rComb wHas) (fun d ↦ rComb (wIdx d))
        (fun l ↦ rComb (wOut l)) hdN.has_ne_out hdN.idx_ne_out
theorem uFwdWG_mulVec_ket {M n : ℕ} (rComb : QRegister M n) :
    ∀ (K : DiagCtxWG M) (β : BitAssignment n),
      (uFwdWG rComb K).1.mulVec (ket β) =
        ket (p2d_writeReg β rComb (K.fwdBits (fun idx ↦ β (rComb idx))))
  | .hole, β => by
      dsimp only [uFwdWG, DiagCtxWG.fwdBits]
      rw [Submonoid.coe_one, Matrix.one_mulVec, p2d_writeReg_self]
  | .cliffConj c K, β => by
      dsimp only [uFwdWG, DiagCtxWG.fwdBits]
      rw[Submonoid.coe_mul, ← Matrix.mulVec_mulVec, CliffProg.toCircuit_eval_ket,
          cliffProg_onRegister_eval, uFwdWG_mulVec_ket rComb K]
      have hRead : (fun idx ↦ p2d_writeReg β rComb (c.eval (fun i ↦ β (rComb i))) (rComb idx)) =
          c.eval (fun i ↦ β (rComb i)) := funext fun idx ↦ p2d_writeReg_apply_reg _ _ _ idx
      rw [hRead, p2d_writeReg_writeReg]
  | .tempAnd c₁ c₂ anc _ h₁a h₂a K, β => by
      dsimp only [uFwdWG, DiagCtxWG.fwdBits]
      rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, uTempAnd_mulVec_ket,
          p2d_writeReg_update rComb β anc, uFwdWG_mulVec_ket rComb K]
      have hRead : (fun idx ↦ p2d_writeReg β rComb (Function.update (fun i ↦ β (rComb i)) anc
          (β (rComb anc) + β (rComb c₁) * β (rComb c₂))) (rComb idx)) = Function.update
          (fun i ↦ β (rComb i)) anc (β (rComb anc) + β (rComb c₁) * β (rComb c₂)) := funext
          fun idx ↦ p2d_writeReg_apply_reg _ _ _ idx
      rw [hRead, p2d_writeReg_writeReg]
  | .wStateTree k wIdx wOut _ hd K, β => by
      dsimp only [uFwdWG, DiagCtxWG.fwdBits]
      rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, uOneHotUncond_mulVec_ket]
      let γ := fun idx ↦ β (rComb idx)
      have hIdxEq : idxValD (fun d ↦ rComb (wIdx d)) β = idxValD wIdx γ := by
        rw [idxValD_eq_bitsVal, idxValD_eq_bitsVal]
      have hjEq : (⟨idxValD (fun d ↦ rComb (wIdx d)) β,
          idxValD_lt_two_pow (fun d ↦ rComb (wIdx d)) β⟩ : Fin (2 ^ (k + 1))) =
          ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩ := Fin.ext hIdxEq
      rw [hjEq, p2d_writeReg_update rComb β _ _, uFwdWG_mulVec_ket rComb K]
      have hRead : (fun idx ↦ p2d_writeReg β rComb
          (Function.update γ (wOut ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩)
            (γ (wOut ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩) + 1)) (rComb idx)) =
          Function.update γ (wOut ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩)
            (γ (wOut ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩) + 1) :=
        funext fun idx ↦ p2d_writeReg_apply_reg _ _ _ idx
      rw [hRead, p2d_writeReg_writeReg]
  | .wStateTreeCohGate1 k wHas wIdx wOut _ hd K, β => by
      dsimp only [uFwdWG, DiagCtxWG.fwdBits]
      rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec, uOneHotToggle_mulVec_ket]
      let γ := fun idx ↦ β (rComb idx)
      have hIdxEq : idxValD (fun d ↦ rComb (wIdx d)) β = idxValD wIdx γ := by
        rw [idxValD_eq_bitsVal, idxValD_eq_bitsVal]
      have hToggle : toggleOneHotBits (rComb wHas) (fun d ↦ rComb (wIdx d))
          (fun l ↦ rComb (wOut l)) β = p2d_writeReg β rComb (Function.update γ (wOut ⟨idxValD
          wIdx γ, idxValD_lt_two_pow wIdx γ⟩) (γ (wOut ⟨idxValD wIdx γ, idxValD_lt_two_pow
          wIdx γ⟩) + γ wHas)) := by
        dsimp only [toggleOneHotBits]
        rw [dite_eq_left (idxValD_lt_two_pow _ β)]
        have hjEq : (⟨idxValD (fun d ↦ rComb (wIdx d)) β,
            idxValD_lt_two_pow (fun d ↦ rComb (wIdx d)) β⟩ : Fin (2 ^ (k + 1))) =
            ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩ := Fin.ext hIdxEq
        rw [hjEq]
        exact p2d_writeReg_update rComb β _ _
      rw [hToggle, uFwdWG_mulVec_ket rComb K]
      have hRead : (fun idx ↦ p2d_writeReg β rComb
          (Function.update γ (wOut ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩)
            (γ (wOut ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩) + γ wHas)) (rComb idx)) =
          Function.update γ (wOut ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩)
            (γ (wOut ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩) + γ wHas) :=
        funext fun idx ↦ p2d_writeReg_apply_reg _ _ _ idx
      rw [hRead, p2d_writeReg_writeReg]
theorem cliffProg_inv_mul_self {M n : ℕ} (rComb : QRegister M n) (c : CliffProg M) :
    (c.inv.onRegister rComb).toCircuit.eval * (c.onRegister rComb).toCircuit.eval = 1 := by
  apply Subtype.ext; apply matrix_ext_ket; intro β
  simp only [Submonoid.coe_mul, Submonoid.coe_one, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
    CliffProg.toCircuit_eval_ket, cliffProg_onRegister_eval]
  have hRead : (fun idx ↦ p2d_writeReg β rComb (c.eval (fun i ↦ β (rComb i))) (rComb idx)) =
      c.eval (fun i ↦ β (rComb i)) := funext fun idx ↦ p2d_writeReg_apply_reg _ _ _ idx
  rw [hRead, p2d_writeReg_writeReg, CliffProg.inv_eval, p2d_writeReg_self]
theorem cliffProg_self_mul_inv {M n : ℕ} (rComb : QRegister M n) (c : CliffProg M) :
    (c.onRegister rComb).toCircuit.eval * (c.inv.onRegister rComb).toCircuit.eval = 1 := by
  let Uc := (c.onRegister rComb).toCircuit.eval
  let Ucinv := (c.inv.onRegister rComb).toCircuit.eval
  have hL : Ucinv * Uc = 1 := cliffProg_inv_mul_self rComb c
  calc Uc * Ucinv
      = 1 * (Uc * Ucinv) := (one_mul _).symm
    _ = (Ucinv⁻¹ * Ucinv) * (Uc * Ucinv) := by rw [inv_mul_cancel]
    _ = Ucinv⁻¹ * (Ucinv * Uc) * Ucinv := by simp only [mul_assoc]
    _ = Ucinv⁻¹ * 1 * Ucinv := by rw [hL]
    _ = 1 := by rw [mul_one, inv_mul_cancel]
theorem uFwdWG_comm_of_commutesWith {M n : ℕ} (rComb : QRegister M n) (U₀ : Unitary (2 ^ n)) :
    ∀ {K : DiagCtxWG M}, DiagCtxWGCommutesWith rComb U₀ K →
      uFwdWG rComb K * U₀ = U₀ * uFwdWG rComb K
  | .hole, _ => by dsimp only [uFwdWG]; rw [one_mul, mul_one]
  | .cliffConj c K₁, ⟨hCommInv, hK₁⟩ => by
      have ih := uFwdWG_comm_of_commutesWith rComb U₀ hK₁
      have hCommC : (c.onRegister rComb).toCircuit.eval * U₀ =
          U₀ * (c.onRegister rComb).toCircuit.eval := by
        calc (c.onRegister rComb).toCircuit.eval * U₀
            = (c.onRegister rComb).toCircuit.eval * U₀ *
                ((c.inv.onRegister rComb).toCircuit.eval * (c.onRegister rComb).toCircuit.eval) :=
                    by
              rw [cliffProg_inv_mul_self rComb c, mul_one]
          _ = (c.onRegister rComb).toCircuit.eval *
                (U₀ * (c.inv.onRegister rComb).toCircuit.eval) *
                (c.onRegister rComb).toCircuit.eval := by simp only [mul_assoc]
          _ = ((c.onRegister rComb).toCircuit.eval * (c.inv.onRegister rComb).toCircuit.eval) *
                (U₀ * (c.onRegister rComb).toCircuit.eval) := by
              rw [← hCommInv]; simp only [mul_assoc]
          _ = U₀ * (c.onRegister rComb).toCircuit.eval := by
              rw [cliffProg_self_mul_inv rComb c, one_mul]
      dsimp only [uFwdWG]
      rw [mul_assoc, hCommC, ← mul_assoc, ih, mul_assoc]
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K₁, ⟨hCommToff, _, hK₁⟩ => by
      have ih := uFwdWG_comm_of_commutesWith rComb U₀ hK₁
      dsimp only [uFwdWG]
      rw [uTempAnd_eq_toff (rComb c₁) (rComb c₂) (rComb anc)
            (rComb.wires.injective.ne h₁₂) (rComb.wires.injective.ne h₁a) (rComb.wires.injective.ne
                h₂a),
          mul_assoc, hCommToff, ← mul_assoc, ih, mul_assoc]
  | .wStateTree _ _ _ _ _ K₁, ⟨hCommOH, _, hK₁⟩ => by
      have ih := uFwdWG_comm_of_commutesWith rComb U₀ hK₁
      dsimp only [uFwdWG]
      rw [mul_assoc, hCommOH, ← mul_assoc, ih, mul_assoc]
  | .wStateTreeCohGate1 _ _ _ _ _ _ K₁, ⟨hCommOH, _, hK₁⟩ => by
      have ih := uFwdWG_comm_of_commutesWith rComb U₀ hK₁
      dsimp only [uFwdWG]
      rw [mul_assoc, hCommOH, ← mul_assoc, ih, mul_assoc]
theorem uFwdWG_comm_embedUnitary {M n kSub : ℕ} (rSub : QRegister kSub n)
    (V : Unitary (2 ^ kSub)) (rComb : QRegister M n) (base : ℕ) (hOutNotSub : ∀ idx : Wire M,
    base ≤ idx.val → rComb idx ∉ Set.range rSub.wires) (hCombPres : ∀ (idx : Wire M) (g : Fin
    (2 ^ n)) (y : Fin (2 ^ kSub)), V.1 y (rSub.extractIndex g) ≠ 0 → basisBits n
    (rSub.replaceIndex g y) (rComb idx) = basisBits n g (rComb idx)) {K : DiagCtxWG M}
    (hW : DiagCtxWGWritesAbove base K) : uFwdWG rComb K * rSub.embedUnitary V =
    rSub.embedUnitary V * uFwdWG rComb K := uFwdWG_comm_of_commutesWith rComb
    (rSub.embedUnitary V) (diagCtxWGWritesAbove_to_commutesWith rSub V rComb base hOutNotSub
    hCombPres hW)
/-- Local dynamic-circuit lowering of `DiagCtxWG M` around `inner` (via wire-group routers). -/
noncomputable def toDynWGLocal {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n)
    (inner : DynamicCircuit Var n) : DiagCtxWG M → DynamicCircuit Var n
  | .hole => inner
  | .cliffConj c K =>
      .seq (.circuit (c.onRegister rComb).toCircuit)
        (.seq (toDynWGLocal v rComb inner K) (.circuit (c.inv.onRegister rComb).toCircuit))
  | .tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K =>
      .seq (DynamicCircuit.andCompute (rComb c₁) (rComb c₂) (rComb anc)
              (rComb.wires.injective.ne h₁a) (rComb.wires.injective.ne h₂a))
        (.seq (toDynWGLocal v rComb inner K)
          (DynamicCircuit.andUncompute v (rComb c₁) (rComb c₂) (rComb anc)
            (rComb.wires.injective.ne h₁₂)))
  | .wStateTree k wIdx wOut qEnc _ K =>
      .seq (wStateComputeUncondPow2 k v
              (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l)) (rComb qEnc))
        (.seq (toDynWGLocal v rComb inner K)
          (wStateUncomputeUncondPow2 k v (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l))))
  | .wStateTreeCohGate1 k wHas wIdx wOut qEnc _ K =>
      .seq (wStateComputeCohGate1 k v (rComb wHas)
              (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l)) (rComb qEnc))
        (.seq (toDynWGLocal v rComb inner K)
          (wStateUncomputeCohGate1 k v (rComb wHas)
            (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l))))
theorem toDynWGLocal_count_toff {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n)
    (inner : DynamicCircuit Var n) (K : DiagCtxWG M) :
    (toDynWGLocal v rComb inner K).count TOFF = inner.count TOFF := by
  induction K with
  | hole => rfl
  | cliffConj c K ih =>
      simp [toDynWGLocal, DynamicCircuit.count,
        CliffProg.toCircuit_count_toff (c.onRegister rComb),
        CliffProg.toCircuit_count_toff (c.inv.onRegister rComb), ih]
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K ih =>
      have h1 : (DynamicCircuit.andCompute (Var := Var) (rComb c₁) (rComb c₂) (rComb anc)
          (rComb.wires.injective.ne h₁a) (rComb.wires.injective.ne h₂a)).count TOFF = 0 := rfl
      have h2 : (DynamicCircuit.andUncompute v (rComb c₁) (rComb c₂) (rComb anc)
          (rComb.wires.injective.ne h₁₂)).count TOFF = 0 := rfl
      dsimp only [toDynWGLocal, DynamicCircuit.count]
      rw [h1, h2, ih]; omega
  | wStateTree k wIdx wOut qEnc _ K ih =>
      obtain ⟨_, h1⟩ := count_wStateComputeUncondPow2 k v
        (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l)) (rComb qEnc)
      obtain ⟨_, h2⟩ := count_wStateUncomputeUncondPow2 k v
        (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l))
      dsimp only [toDynWGLocal, DynamicCircuit.count]
      rw [h1, h2, ih]; omega
  | wStateTreeCohGate1 k wHas wIdx wOut qEnc _ K ih =>
      obtain ⟨_, h1⟩ := count_wStateComputeCohGate1 k v
        (rComb wHas) (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l)) (rComb qEnc)
      obtain ⟨_, h2⟩ := count_wStateUncomputeCohGate1 k v
        (rComb wHas) (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l))
      dsimp only [toDynWGLocal, DynamicCircuit.count]
      rw [h1, h2, ih]; omega
theorem toDynWGLocal_count_t {Var : Type} {M n : ℕ} (v : Var) (rComb : QRegister M n)
    (inner : DynamicCircuit Var n) (K : DiagCtxWG M) :
    (toDynWGLocal v rComb inner K).count T = K.countT + inner.count T := by
  induction K with
  | hole => simp [toDynWGLocal, DiagCtxWG.countT]
  | cliffConj c K ih =>
      simp [toDynWGLocal, DiagCtxWG.countT, DynamicCircuit.count,
        CliffProg.toCircuit_count_t (c.onRegister rComb),
        CliffProg.toCircuit_count_t (c.inv.onRegister rComb), ih]
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K ih =>
      have h1 : (DynamicCircuit.andCompute (Var := Var) (rComb c₁) (rComb c₂) (rComb anc)
          (rComb.wires.injective.ne h₁a) (rComb.wires.injective.ne h₂a)).count T = 4 := rfl
      have h2 : (DynamicCircuit.andUncompute v (rComb c₁) (rComb c₂) (rComb anc)
          (rComb.wires.injective.ne h₁₂)).count T = 0 := rfl
      dsimp only [toDynWGLocal, DiagCtxWG.countT, DynamicCircuit.count]
      rw [h1, h2, ih]; omega
  | wStateTree k wIdx wOut qEnc _ K ih =>
      obtain ⟨h1, _⟩ := count_wStateComputeUncondPow2 k v
        (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l)) (rComb qEnc)
      obtain ⟨h2, _⟩ := count_wStateUncomputeUncondPow2 k v
        (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l))
      dsimp only [toDynWGLocal, DiagCtxWG.countT, DynamicCircuit.count]
      rw [h1, h2, ih]; omega
  | wStateTreeCohGate1 k wHas wIdx wOut qEnc _ K ih =>
      obtain ⟨h1, _⟩ := count_wStateComputeCohGate1 k v
        (rComb wHas) (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l)) (rComb qEnc)
      obtain ⟨h2, _⟩ := count_wStateUncomputeCohGate1 k v
        (rComb wHas) (fun d ↦ rComb (wIdx d)) (fun l ↦ rComb (wOut l))
      dsimp only [toDynWGLocal, DiagCtxWG.countT, DynamicCircuit.count]
      rw [h1, h2, ih]; omega
/-- Master symmetric compute-inner-MBU-uncompute `SubspaceStep` theorem for `toDynWGLocal`:
steps `R_in ↦ R_out` whenever both `R_in` and `R_out` satisfy `K.ValidAt` on `rComb` and
`inner` steps `(uFwdWG rComb K).1 * R_in ↦ (uFwdWG rComb K).1 * R_out`. -/
private theorem subspaceStep_toDynWGLocal_step {Var : Type} [Fintype Var] [DecidableEq Var]
    {M n : ℕ} [NeZero (2 ^ n)] {rComb : QRegister M n} {P_in : BitAssignment M → Prop}
    {K : DiagCtxWG M} {R_in R_out : Operator (2 ^ n)} {uStep : Unitary (2 ^ n)}
    {fStep : BitAssignment n → BitAssignment n} {dComp dMid dUnc inner : DynamicCircuit Var n}
    (hKet : ∀ β, uStep.1.mulVec (ket β) = ket (fStep β)) (hImp : ∀ β, P_in (fun idx ↦ β (rComb
    idx)) → K.ValidAt (fun idx ↦ fStep β (rComb idx)))
    (hIn : SupportedOn (fun β ↦ P_in (fun idx ↦ β (rComb idx))) R_in)
    (hOut : SupportedOn (fun β ↦ P_in (fun idx ↦ β (rComb idx))) R_out) (hInner : SubspaceStep
    (((uFwdWG rComb K).1 * uStep.1) * R_in) (((uFwdWG rComb K).1 * uStep.1) * R_out) inner)
    (ih : ∀ {A B : Operator (2 ^ n)}, SupportedOn (fun β ↦ K.ValidAt (fun idx ↦ β (rComb
    idx))) A → SupportedOn (fun β ↦ K.ValidAt (fun idx ↦ β (rComb idx))) B → SubspaceStep
    ((uFwdWG rComb K).1 * A) ((uFwdWG rComb K).1 * B) inner → SubspaceStep A B dMid)
    (sComp : SubspaceStep R_in (uStep.1 * R_in) dComp)
    (sUnc : SubspaceStep (uStep.1 * R_out) R_out dUnc) : SubspaceStep R_in R_out
    (.seq dComp (.seq dMid dUnc)) :=
  sComp.seq ((ih (supportedOn_unitary_mul uStep.1 _ hKet hImp hIn)
    (supportedOn_unitary_mul uStep.1 _ hKet hImp hOut)
    (by simpa only [Matrix.mul_assoc] using hInner)).seq sUnc)
private theorem oneHot_validAt_imp {M n k : ℕ} (rComb : QRegister M n)
    (wIdx : Fin (k + 1) → Wire M) (wOut : Fin (2 ^ (k + 1)) → Wire M)
    (valBit : BitAssignment M → ZMod 2) (K : DiagCtxWG M) (β : BitAssignment n) (hV :
    K.ValidAt (Function.update (fun idx ↦ β (rComb idx)) (wOut ⟨idxValD wIdx (fun idx ↦ β
    (rComb idx)), idxValD_lt_two_pow wIdx _⟩) (β (rComb (wOut ⟨idxValD wIdx (fun idx ↦ β
    (rComb idx)), idxValD_lt_two_pow wIdx _⟩)) + valBit (fun idx ↦ β (rComb idx))))) :
    K.ValidAt (fun idx ↦ Function.update β (rComb (wOut ⟨idxValD (fun d ↦ rComb (wIdx d)) β,
    idxValD_lt_two_pow _ β⟩)) (β (rComb (wOut ⟨idxValD (fun d ↦ rComb (wIdx d)) β,
    idxValD_lt_two_pow _ β⟩)) + valBit (fun idx ↦ β (rComb idx))) (rComb idx)) := by
  have hjEq : (⟨idxValD (fun d ↦ rComb (wIdx d)) β, idxValD_lt_two_pow _ β⟩ : Fin (2 ^ (k + 1))) =
      ⟨idxValD wIdx (fun idx ↦ β (rComb idx)), idxValD_lt_two_pow wIdx _⟩ :=
    Fin.ext (by
      dsimp only
      rw [idxValD_eq_bitsVal, idxValD_eq_bitsVal])
  rw [hjEq, p2d_writeReg_update,
    show (fun idx ↦ p2d_writeReg β rComb _ (rComb idx)) = _ from
      funext fun idx ↦ p2d_writeReg_apply_reg _ _ _ idx]
  exact hV
theorem subspaceStep_toDynWGLocal {Var : Type} [Fintype Var] [DecidableEq Var] {M n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rComb : QRegister M n) (inner : DynamicCircuit Var n) : ∀
    (K : DiagCtxWG M) {R_in R_out : Operator (2 ^ n)}, SupportedOn
    (fun β ↦ K.ValidAt (fun idx ↦ β (rComb idx))) R_in → SupportedOn
    (fun β ↦ K.ValidAt (fun idx ↦ β (rComb idx))) R_out → SubspaceStep
    ((uFwdWG rComb K).1 * R_in) ((uFwdWG rComb K).1 * R_out) inner → SubspaceStep R_in R_out
    (toDynWGLocal v rComb inner K) := by
  intro K
  induction K with
  | hole =>
      intro R_in R_out _ _ hInner
      simpa only [toDynWGLocal, uFwdWG, Submonoid.coe_one, Matrix.one_mul] using hInner
  | cliffConj c K ih =>
      intro R_in R_out hIn hOut hInner
      dsimp only [toDynWGLocal, uFwdWG, Submonoid.coe_mul] at hInner ⊢
      let cPre := (c.onRegister rComb).toCircuit
      let cPost := (c.inv.onRegister rComb).toCircuit
      refine subspaceStep_toDynWGLocal_step
        (fun β ↦ (CliffProg.toCircuit_eval_ket _ β).trans (congrArg ket (cliffProg_onRegister_eval
            rComb c β)))
        (fun β hV ↦ by
          rw [show (fun idx ↦ p2d_writeReg β rComb (c.eval fun i ↦ β (rComb i)) (rComb idx)) =
            c.eval fun i ↦ β (rComb i) from funext fun idx ↦ p2d_writeReg_apply_reg _ _ _ idx]
          exact hV)
        hIn hOut hInner ih (subspaceStep_of_circuit (Var := Var) R_in cPre)
        (subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) _ cPost) ?_)
      rw [← Matrix.mul_assoc,
          show cPost.eval.1 * cPre.eval.1 = 1 from congrArg Subtype.val (cliffProg_inv_mul_self
              rComb c),
          Matrix.one_mul]
  | tempAnd c₁ c₂ anc h₁₂ h₁a h₂a K ih =>
      intro R_in R_out hIn hOut hInner
      dsimp only [toDynWGLocal, uFwdWG, Submonoid.coe_mul] at hInner ⊢
      exact subspaceStep_toDynWGLocal_step (uTempAnd_mulVec_ket _ _ _ _ _)
        (fun β ⟨_, hV⟩ ↦ by
          rw [p2d_writeReg_update, show (fun idx ↦ p2d_writeReg β rComb _ (rComb idx)) = _ from
            funext fun idx ↦ p2d_writeReg_apply_reg _ _ _ idx]
          exact hV)
        hIn hOut hInner ih
        (subspaceStep_andCompute (Var := Var) (rComb c₁) (rComb c₂) (rComb anc)
          (rComb.wires.injective.ne h₁₂) (rComb.wires.injective.ne h₁a) (rComb.wires.injective.ne
              h₂a)
          R_in fun A B hAB ↦ hIn A B fun β hV ↦ hAB β hV.1)
        (subspaceStep_andUncompute v (rComb c₁) (rComb c₂) (rComb anc)
          (rComb.wires.injective.ne h₁₂) (rComb.wires.injective.ne h₁a) (rComb.wires.injective.ne
              h₂a)
          R_out fun A B hAB ↦ hOut A B fun β hV ↦ hAB β hV.1)
  | wStateTree k wIdx wOut qEnc hd K ih =>
      intro R_in R_out hIn hOut hInner
      dsimp only [toDynWGLocal, uFwdWG, Submonoid.coe_mul] at hInner ⊢
      let hdN := wUncondDisjProp_onRegister rComb hd
      exact subspaceStep_toDynWGLocal_step (uOneHotUncond_mulVec_ket _ _ _) (fun β ⟨_, hV⟩ ↦
        oneHot_validAt_imp rComb wIdx wOut (fun _ ↦ 1) K β hV) hIn hOut hInner ih
        (subspaceStep_wStateComputeUncondPow2 k v _ _ (rComb qEnc) hdN R_in fun A B hAB ↦ hIn
        A B fun β hV ↦ hAB β hV.1) (subspaceStep_wStateUncomputeUncondPow2 k v _ _ ⟨hdN.1,
        hdN.2.2.1⟩ R_out fun A B hAB ↦ hOut A B fun β hV ↦ hAB β hV.1.1)
  | wStateTreeCohGate1 k wHas wIdx wOut qEnc hd K ih =>
      intro R_in R_out hIn hOut hInner
      dsimp only [toDynWGLocal, uFwdWG, Submonoid.coe_mul] at hInner ⊢
      let hdN := wRouterDisj_onRegister rComb hd
      exact subspaceStep_toDynWGLocal_step (uOneHotToggle_mulVec_ket _ _ _ _ _)
        (fun β ⟨_, hV⟩ ↦ by
          dsimp only [toggleOneHotBits]
          rw [dite_eq_left (idxValD_lt_two_pow _ β)]
          exact oneHot_validAt_imp rComb wIdx wOut (fun γ ↦ γ wHas) K β hV)
        hIn hOut hInner ih
        (subspaceStep_wStateComputeCohGate1 k v (rComb wHas) _ _ (rComb qEnc) hdN R_in
          fun A B hAB ↦ hIn A B fun β hV ↦ hAB β hV.1)
        (subspaceStep_wStateUncomputeCohGate1 k v (rComb wHas) _ _
          hdN.has_ne_out hdN.idx_ne_out hdN.out_inj R_out
          fun A B hAB ↦ hOut A B fun β hV ↦ hAB β hV.1.1)
-- ============================================================================
-- Section 2A: Self-Contained `Slot18Lens`, `uLensLoad`, `uLensWrite`, `uLensSwap`,
--             `P_slot0`, `restrictOfCommSlot0`, & `setTableOp` Algebra
-- ============================================================================
/-- Data selector `[0 .. kData)` inside `kData + 18`. -/
abbrev selDataInAct (kData : ℕ) : QRegister kData (kData + 18) :=
  BoothOpt_StageBPartnerCoreShave.selDataInAct kData
/-- Measurement/partner selector `[kData .. kData + 18)` inside `kData + 18`. -/
def selMeasInAct (kData : ℕ) : QRegister 18 (kData + 18) :=
  QRegister.block kData 18 (by omega)
theorem selDataInAct_apply {kData : ℕ} (i : Fin kData) : selDataInAct kData i = Fin.castAdd 18
    i := BoothOpt_StageBPartnerCoreShave.selDataInAct_apply i
theorem selMeasInAct_apply {kData : ℕ} (j : Fin 18) :
    selMeasInAct kData j = Fin.natAdd kData j :=
  Fin.ext (by simp [selMeasInAct, QRegister.block])
theorem selDataInAct_disj_selMeasInAct (kData : ℕ) :
    (selDataInAct kData).DisjointWires (selMeasInAct kData) := by
  rw [QRegister.disjoint_iff]
  intro i j h
  rw [selDataInAct_apply, selMeasInAct_apply] at h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  have := i.isLt; omega
theorem concat_compose_selDataInAct {n kData : ℕ}
    (rData : QRegister kData n) (rMeas : QRegister 18 n) (hDM : rData.DisjointWires rMeas) :
    (rData.concat rMeas hDM).compose (selDataInAct kData) = rData := by
  ext i
  exact congrArg Fin.val ((congrArg (rData.concat rMeas hDM).wires (selDataInAct_apply i)).trans
    (QRegister.concat_apply_left rData rMeas hDM i))
theorem concat_compose_selMeasInAct {n kData : ℕ}
    (rData : QRegister kData n) (rMeas : QRegister 18 n) (hDM : rData.DisjointWires rMeas) :
    (rData.concat rMeas hDM).compose (selMeasInAct kData) = rMeas := by
  ext j
  exact congrArg Fin.val ((congrArg (rData.concat rMeas hDM).wires (selMeasInAct_apply j)).trans
    (QRegister.concat_apply_right rData rMeas hDM j))
/-- Variable-`N` injectivity of `basisBits N` (prevents `basisBitsEquiv (kData + 18)` from
  unfolding `18` steps). -/
theorem basisBits_inj {N : ℕ} {x y : Fin (2 ^ N)}
    (h : ∀ w : Fin N, basisBits N x w = basisBits N y w) : x = y :=
  (basisBitsEquiv N).injective (funext h)
/-- Bitwise XOR on `Fin (2 ^ 18)` via `basisBitsEquiv 18`. -/
noncomputable def xor18 (x y : Fin (2 ^ 18)) : Fin (2 ^ 18) :=
  (basisBitsEquiv 18).symm fun j ↦ basisBits 18 x j + basisBits 18 y j
@[simp] theorem basisBits_xor18 (x y : Fin (2 ^ 18)) (j : Fin 18) :
    basisBits 18 (xor18 x y) j = basisBits 18 x j + basisBits 18 y j :=
  congrFun ((basisBitsEquiv 18).apply_symm_apply _) j
theorem basisBits18_zero (j : Fin 18) : basisBits 18 (0 : Fin (2 ^ 18)) j = 0 := by
  simp [-Nat.reducePow, basisBits_eq_div_mod]
@[simp] theorem xor18_zero_right (x : Fin (2 ^ 18)) : xor18 x 0 = x := by
  refine basisBits_inj fun j ↦ ?_
  rw [basisBits_xor18, basisBits18_zero, add_zero]
@[simp] theorem xor18_zero_left (y : Fin (2 ^ 18)) : xor18 0 y = y := by
  refine basisBits_inj fun j ↦ ?_
  rw [basisBits_xor18, basisBits18_zero, zero_add]
@[simp] theorem xor18_self (x : Fin (2 ^ 18)) : xor18 x x = 0 := by
  refine basisBits_inj fun j ↦ ?_
  rw [basisBits_xor18, basisBits18_zero, CharTwo.add_self_eq_zero]
@[simp] theorem xor18_cancel_right (x y : Fin (2 ^ 18)) : xor18 (xor18 x y) y = x := by
  refine basisBits_inj fun j ↦ ?_
  rw [basisBits_xor18, basisBits_xor18, CharTwo.add_cancel_right]
/-- Abstract 18-bit slot lens `(tbl, updSlot)` on `Fin (2 ^ kData)` capturing any indexed slot
  bank. -/
structure Slot18Lens (kData : ℕ) where
  tbl : Fin (2 ^ kData) → Fin (2 ^ 18)
  updSlot : Fin (2 ^ kData) → Fin (2 ^ 18) → Fin (2 ^ kData)
  get_put : ∀ d v, tbl (updSlot d v) = v
  put_get : ∀ d, updSlot d (tbl d) = d
  put_put : ∀ d v₁ v₂, updSlot (updSlot d v₁) v₂ = updSlot d v₂
/-- Forward load map `(d, y) ↦ (d, y ⊕ tbl d)`. -/
noncomputable def lensLoadPerm {kData : ℕ} (L : Slot18Lens kData)
    (p : Fin (2 ^ kData) × Fin (2 ^ 18)) : Fin (2 ^ kData) × Fin (2 ^ 18) :=
  (p.1, xor18 p.2 (L.tbl p.1))
/-- Reverse write map `(d, y) ↦ (updSlot d (tbl d ⊕ y), y)`. -/
noncomputable def lensWritePerm {kData : ℕ} (L : Slot18Lens kData)
    (p : Fin (2 ^ kData) × Fin (2 ^ 18)) : Fin (2 ^ kData) × Fin (2 ^ 18) :=
  (L.updSlot p.1 (xor18 (L.tbl p.1) p.2), p.2)
/-- True swap map `(d, y) ↦ (updSlot d y, tbl d)`. -/
noncomputable def lensSwapPerm {kData : ℕ} (L : Slot18Lens kData)
    (p : Fin (2 ^ kData) × Fin (2 ^ 18)) : Fin (2 ^ kData) × Fin (2 ^ 18) :=
  (L.updSlot p.1 p.2, L.tbl p.1)
theorem lensLoadPerm_involutive {kData : ℕ} (L : Slot18Lens kData) :
    Function.Involutive (lensLoadPerm L) := by
  rintro ⟨d, y⟩; dsimp only [lensLoadPerm]; rw [xor18_cancel_right]
theorem lensWritePerm_involutive {kData : ℕ} (L : Slot18Lens kData) :
    Function.Involutive (lensWritePerm L) := by
  rintro ⟨d, y⟩; dsimp only [lensWritePerm]
  rw [L.get_put, L.put_put, xor18_cancel_right, L.put_get]
theorem lensSwapPerm_involutive {kData : ℕ} (L : Slot18Lens kData) :
    Function.Involutive (lensSwapPerm L) := by
  rintro ⟨d, y⟩; dsimp only [lensSwapPerm]; rw [L.get_put, L.put_put, L.put_get]
@[simp] theorem lensWrite_lensLoad_zero_eq_swap {kData : ℕ} (L : Slot18Lens kData)
    (d : Fin (2 ^ kData)) :
    lensWritePerm L (lensLoadPerm L (d, 0)) = lensSwapPerm L (d, 0) := by
  dsimp only [lensLoadPerm, lensWritePerm, lensSwapPerm]; rw [xor18_zero_left, xor18_self]
@[simp] theorem lensWrite_lensSwap_zero_eq_dup {kData : ℕ} (L : Slot18Lens kData)
    (d' : Fin (2 ^ kData)) : lensWritePerm L (lensSwapPerm L (d', 0)) = (d', L.tbl d') := by
  dsimp only [lensSwapPerm, lensWritePerm]; rw [L.get_put, xor18_zero_left, L.put_put, L.put_get]
/-- Pair extractor splitting `Fin (2 ^ (kData + 18))` into `(d, y)` (`abbrev` so `whnfCore` unfolds
  before `Fin` eta). -/
abbrev extractPair {kData : ℕ} (g : Fin (2 ^ (kData + 18))) : Fin (2 ^ kData) × Fin (2 ^ 18) :=
  ((selDataInAct kData).extractIndex g, (selMeasInAct kData).extractIndex g)
/-- Lifts `F : Fin (2 ^ kData) × Fin (2 ^ 18) → Fin (2 ^ kData) × Fin (2 ^ 18)` to `Fin (2 ^ (kData
  + 18))`. -/
noncomputable def liftPairIdx {kData : ℕ} (F : Fin (2 ^ kData) × Fin (2 ^ 18) → Fin (2 ^
    kData) × Fin (2 ^ 18)) (g : Fin (2 ^ (kData + 18))) : Fin (2 ^ (kData + 18)) :=
  let p := F (extractPair g)
  (selMeasInAct kData).replaceIndex ((selDataInAct kData).replaceIndex g p.1) p.2
@[simp] theorem extractPair_liftPairIdx {kData : ℕ} (F : Fin (2 ^ kData) × Fin (2 ^ 18) → Fin
    (2 ^ kData) × Fin (2 ^ 18)) (g : Fin (2 ^ (kData + 18))) : extractPair (liftPairIdx F g) =
    F (extractPair g) := by
  dsimp only [extractPair, liftPairIdx]
  ext
  · rw [QRegister.extractIndex_replaceIndex_of_disjoint
        (selDataInAct kData) (selMeasInAct kData) (selDataInAct_disj_selMeasInAct kData),
      QRegister.extractIndex_replaceIndex]
  · rw [QRegister.extractIndex_replaceIndex]
@[simp] theorem liftPairIdx_comp {kData : ℕ} (G F : Fin (2 ^ kData) × Fin (2 ^ 18) → Fin (2 ^
    kData) × Fin (2 ^ 18)) (g : Fin (2 ^ (kData + 18))) : liftPairIdx G (liftPairIdx F g) =
    liftPairIdx (fun p ↦ G (F p)) g := by
  have hEx := extractPair_liftPairIdx F g
  dsimp only [liftPairIdx] at hEx ⊢
  rw [hEx, QRegister.replaceIndex_comm_of_disjoint
        (selDataInAct kData) (selMeasInAct kData) (selDataInAct_disj_selMeasInAct kData),
      QRegister.replaceIndex_replaceIndex, QRegister.replaceIndex_replaceIndex]
@[simp] theorem liftPairIdx_id {kData : ℕ} (g : Fin (2 ^ (kData + 18))) :
    liftPairIdx id g = g := by
  dsimp only [liftPairIdx, extractPair, id]
  rw [QRegister.replaceIndex_extractIndex, QRegister.replaceIndex_extractIndex]
theorem liftPairIdx_involutive {kData : ℕ}
    {F : Fin (2 ^ kData) × Fin (2 ^ 18) → Fin (2 ^ kData) × Fin (2 ^ 18)}
    (hF : Function.Involutive F) :
    Function.Involutive (liftPairIdx F) := fun g ↦ by
  rw [liftPairIdx_comp, show (fun p ↦ F (F p)) = id from funext hF, liftPairIdx_id]
private theorem sub_kData_lt_18 {kData : ℕ} (w : Fin (kData + 18)) (hw : ¬ w.val < kData) :
    w.val - kData < 18 := by
  have := w.isLt; omega
private theorem selMeasInAct_of_not_lt {kData : ℕ} (w : Fin (kData + 18)) (hw : ¬ w.val < kData) :
    w = selMeasInAct kData ⟨w.val - kData, sub_kData_lt_18 w hw⟩ := by
  rw [selMeasInAct_apply]
  exact Fin.ext (by dsimp; have := w.isLt; omega)
theorem extractPair_injective {kData : ℕ} {x y : Fin (2 ^ (kData + 18))}
    (h : extractPair x = extractPair y) : x = y := by
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  refine basisBits_inj fun w ↦ ?_
  by_cases hw : w.val < kData
  · let i : Fin kData := ⟨w.val, hw⟩
    have hwEq : w = selDataInAct kData i := (selDataInAct_apply i).symm
    have hx := QRegister.basisBits_extractIndex (selDataInAct kData) x i
    have hy := QRegister.basisBits_extractIndex (selDataInAct kData) y i
    rw [hwEq, ← hx, ← hy, h1]
  · let j : Fin 18 := ⟨w.val - kData, sub_kData_lt_18 w hw⟩
    have hwEq : w = selMeasInAct kData j := selMeasInAct_of_not_lt w hw
    have hx := QRegister.basisBits_extractIndex (selMeasInAct kData) x j
    have hy := QRegister.basisBits_extractIndex (selMeasInAct kData) y j
    rw [hwEq, ← hx, ← hy, h2]
/-- Canonical pair embedding `liftPair0 (d, y) : Fin (2 ^ (kData + 18))` (`abbrev` to avoid `Fin`
  eta). -/
noncomputable abbrev liftPair0 {kData : ℕ} (p : Fin (2 ^ kData) × Fin (2 ^ 18)) : Fin
    (2 ^ (kData + 18)) := liftPairIdx (fun _ ↦ p) ⟨0, Nat.two_pow_pos (kData + 18)⟩
@[simp] theorem extractPair_liftPair0 {kData : ℕ} (p : Fin (2 ^ kData) × Fin (2 ^ 18)) :
    extractPair (liftPair0 p) = p :=
  extractPair_liftPairIdx (fun _ ↦ p) ⟨0, Nat.two_pow_pos (kData + 18)⟩
@[simp] theorem liftPair0_extractPair {kData : ℕ} (z : Fin (2 ^ (kData + 18))) : liftPair0
    (extractPair z) = z := extractPair_injective (extractPair_liftPair0 (extractPair z))
theorem liftPair0_zero_of_meas_zero {kData : ℕ} {z : Fin (2 ^ (kData + 18))}
    (hz : (selMeasInAct kData).extractIndex z = 0) :
    liftPair0 ((selDataInAct kData).extractIndex z, 0) = z := by
  rw [show ((selDataInAct kData).extractIndex z, (0 : Fin (2 ^ 18))) = extractPair z from
    Prod.ext rfl hz.symm, liftPair0_extractPair]
/-- Permutation equivalences and unitaries on `Fin (2 ^ (kData + 18))` for `Slot18Lens`. -/
noncomputable def lensLoadEquiv {kData : ℕ} (L : Slot18Lens kData) : Equiv.Perm
    (Fin (2 ^ (kData + 18))) := Equiv.ofBijective (liftPairIdx (lensLoadPerm L))
    (liftPairIdx_involutive (lensLoadPerm_involutive L)).bijective
noncomputable def lensWriteEquiv {kData : ℕ} (L : Slot18Lens kData) : Equiv.Perm
    (Fin (2 ^ (kData + 18))) := Equiv.ofBijective (liftPairIdx (lensWritePerm L))
    (liftPairIdx_involutive (lensWritePerm_involutive L)).bijective
noncomputable def lensSwapEquiv {kData : ℕ} (L : Slot18Lens kData) : Equiv.Perm
    (Fin (2 ^ (kData + 18))) := Equiv.ofBijective (liftPairIdx (lensSwapPerm L))
    (liftPairIdx_involutive (lensSwapPerm_involutive L)).bijective
/-- Unitary `uLensLoad L : Unitary (2 ^ (kData + 18))` for `lensLoadPerm L`. -/
noncomputable def uLensLoad {kData : ℕ} (L : Slot18Lens kData) : Unitary (2 ^ (kData + 18)) :=
    Operator.permutationUnitary (lensLoadEquiv L)
/-- Unitary `uLensWrite L : Unitary (2 ^ (kData + 18))` for `lensWritePerm L`. -/
noncomputable def uLensWrite {kData : ℕ} (L : Slot18Lens kData) : Unitary (2 ^ (kData + 18))
    := Operator.permutationUnitary (lensWriteEquiv L)
/-- Unitary `uLensSwap L : Unitary (2 ^ (kData + 18))` for `lensSwapPerm L`. -/
noncomputable def uLensSwap {kData : ℕ} (L : Slot18Lens kData) : Unitary (2 ^ (kData + 18)) :=
    Operator.permutationUnitary (lensSwapEquiv L)
theorem mul_basisOutcomeProjector_zero_eq_of_eq_on_zero {n k : ℕ}
    (r : QRegister k n) (A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (h : ∀ i j : Fin (2 ^ n), r.extractIndex j = 0 → A i j = B i j) :
    A * r.basisOutcomeProjector 0 = B * r.basisOutcomeProjector 0 := by
  ext i j
  rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal, Matrix.mul_diagonal]
  by_cases hj : r.extractIndex j = 0
  · rw [ite_eq_left hj, mul_one, mul_one, h i j hj]
  · rw [ite_eq_right hj, mul_zero, mul_zero]
theorem uLensWrite_mul_uLensLoad_projZero_eq_uLensSwap {kData : ℕ} (L : Slot18Lens kData) :
    (uLensWrite L * uLensLoad L).1 * (selMeasInAct kData).basisOutcomeProjector 0 =
      (uLensSwap L).1 * (selMeasInAct kData).basisOutcomeProjector 0 := by
  have hMul : uLensWrite L * uLensLoad L =
      Operator.permutationUnitary (lensWriteEquiv L * lensLoadEquiv L) :=
    (OperatorExt.permutationUnitary_mul (lensWriteEquiv L) (lensLoadEquiv L)).symm
  rw [hMul]
  refine mul_basisOutcomeProjector_zero_eq_of_eq_on_zero (selMeasInAct kData) _ _ fun i j hj0 ↦ ?_
  dsimp only [uLensSwap]
  rw [permUnitary_apply, permUnitary_apply]
  have hEq : (lensWriteEquiv L * lensLoadEquiv L) j = lensSwapEquiv L j := by
    dsimp only [lensWriteEquiv, lensLoadEquiv, lensSwapEquiv]
    rw [Equiv.Perm.mul_apply, Equiv.ofBijective_apply, Equiv.ofBijective_apply,
        Equiv.ofBijective_apply, liftPairIdx_comp]
    dsimp only [liftPairIdx, extractPair]
    rw [hj0, lensWrite_lensLoad_zero_eq_swap]
  rw [hEq]
theorem uLensWrite_mul_uLensSwap_projZero_eq_setTableOp {kData : ℕ} (L : Slot18Lens kData) :
    (uLensWrite L * uLensSwap L).1 * (selMeasInAct kData).basisOutcomeProjector 0 =
      setTableOp (selDataInAct kData) (selMeasInAct kData) L.tbl *
        (selMeasInAct kData).basisOutcomeProjector 0 := by
  have hMul : uLensWrite L * uLensSwap L =
      Operator.permutationUnitary (lensWriteEquiv L * lensSwapEquiv L) :=
    (OperatorExt.permutationUnitary_mul (lensWriteEquiv L) (lensSwapEquiv L)).symm
  rw [hMul]
  refine mul_basisOutcomeProjector_zero_eq_of_eq_on_zero (selMeasInAct kData) _ _ fun i j hj0 ↦ ?_
  rw [permUnitary_apply]
  have hEq : (lensWriteEquiv L * lensSwapEquiv L) j =
      (selMeasInAct kData).replaceIndex j (L.tbl ((selDataInAct kData).extractIndex j)) := by
    dsimp only [lensWriteEquiv, lensSwapEquiv]
    rw [Equiv.Perm.mul_apply, Equiv.ofBijective_apply, Equiv.ofBijective_apply, liftPairIdx_comp]
    dsimp only [liftPairIdx, extractPair]
    rw [hj0, lensWrite_lensSwap_zero_eq_dup, QRegister.replaceIndex_extractIndex]
  rw [hEq]; rfl
theorem lensSwapEquiv_involutive {kData : ℕ} (L : Slot18Lens kData) :
    Function.Involutive (lensSwapEquiv L) := fun g ↦ by
  dsimp only [lensSwapEquiv]
  rw [Equiv.ofBijective_apply, Equiv.ofBijective_apply]
  exact liftPairIdx_involutive (lensSwapPerm_involutive L) g
@[simp] theorem uLensSwap_mul_self {kData : ℕ} (L : Slot18Lens kData) :
    uLensSwap L * uLensSwap L = 1 := by
  dsimp only [uLensSwap]
  rw [← OperatorExt.permutationUnitary_mul,
      show lensSwapEquiv L * lensSwapEquiv L = 1 from
        Equiv.ext fun g ↦ lensSwapEquiv_involutive L g,
      OperatorExt.permutationUnitary_one]
@[simp] theorem uLensSwap_val_mul_self {kData : ℕ} (L : Slot18Lens kData) :
    (uLensSwap L).1 * (uLensSwap L).1 = 1 := by
  rw [← Submonoid.coe_mul, uLensSwap_mul_self, Submonoid.coe_one]
@[simp] theorem uLensSwap_inv {kData : ℕ} (L : Slot18Lens kData) : (uLensSwap L)⁻¹ = uLensSwap
    L := inv_eq_iff_mul_eq_one.mpr (uLensSwap_mul_self L)
-- ============================================================================
-- Section 2B: `P_slot0`, `restrictOfCommSlot0`, `shiftedPartnerLens218`,
--             `Elec3924Preserved`, & `comm_P_slot0_of_elec3924Preserved`
-- ============================================================================
theorem selDataInAct_basisSplitEquiv_snd_eq_iff {kData : ℕ} (x y : Fin (2 ^ (kData + 18))) :
    ((selDataInAct kData).basisSplitEquiv x).2 = ((selDataInAct kData).basisSplitEquiv y).2 ↔
    (selMeasInAct kData).extractIndex x = (selMeasInAct kData).extractIndex y := by
  let selD := selDataInAct kData
  let selM := selMeasInAct kData
  let x' := selD.replaceIndex y (selD.extractIndex x)
  have hx'D : selD.extractIndex x' = selD.extractIndex x :=
    selD.extractIndex_replaceIndex y (selD.extractIndex x)
  have hx'M : selM.extractIndex x' = selM.extractIndex y :=
    QRegister.extractIndex_replaceIndex_of_disjoint selM selD
      (QRegExt.disjointWires_symm (selDataInAct_disj_selMeasInAct kData)) y (selD.extractIndex x)
  have hx'Env : (selD.basisSplitEquiv x').2 = (selD.basisSplitEquiv y).2 := by
    dsimp only [x']; rw [selD.basisSplitEquiv_replaceIndex]
  constructor
  · intro henv
    have h1 : (selD.basisSplitEquiv x').1 = (selD.basisSplitEquiv x).1 := by
      rw [QRegister.basisSplitEquiv_apply_fst, QRegister.basisSplitEquiv_apply_fst, hx'D]
    have hxx' : x' = x := selD.basisSplitEquiv.injective (Prod.ext h1 (hx'Env.trans henv.symm))
    rw [← hxx', hx'M]
  · intro hM
    have hxx' : x' = x := extractPair_injective (Prod.ext hx'D (hx'M.trans hM.symm))
    rw [← hxx', hx'Env]
theorem embedMatrix_selDataInAct_apply {kData : ℕ} (M : Operator (2 ^ kData))
    (i j : Fin (2 ^ (kData + 18))) : ((selDataInAct kData).embedMatrix M) i j = if
    (selMeasInAct kData).extractIndex i = (selMeasInAct kData).extractIndex j then M
    ((selDataInAct kData).extractIndex i) ((selDataInAct kData).extractIndex j) else 0 := by
  rw [QRegister.embedMatrix_apply]
  by_cases hM : (selMeasInAct kData).extractIndex i = (selMeasInAct kData).extractIndex j
  · rw [ite_eq_left ((selDataInAct_basisSplitEquiv_snd_eq_iff i j).mpr hM), ite_eq_left hM, mul_one]
  · rw [ite_eq_right (fun h ↦ hM ((selDataInAct_basisSplitEquiv_snd_eq_iff i j).mp h)),
      ite_eq_right hM, mul_zero]
theorem embedMatrix_selDataInAct_inj_on_Pm {kData : ℕ} {A B : Operator (2 ^ kData)}
    (h : (selDataInAct kData).embedMatrix A * (selMeasInAct kData).basisOutcomeProjector 0 =
      (selDataInAct kData).embedMatrix B * (selMeasInAct kData).basisOutcomeProjector 0) :
    A = B := by
  ext d' d
  let i := liftPair0 (d', (0 : Fin (2 ^ 18)))
  let j := liftPair0 (d, (0 : Fin (2 ^ 18)))
  have hij := congrFun (congrFun h i) j
  obtain ⟨hiD, hi0⟩ := Prod.mk.inj (extractPair_liftPair0 (kData := kData) (d', 0))
  obtain ⟨hjD, hj0⟩ := Prod.mk.inj (extractPair_liftPair0 (kData := kData) (d, 0))
  rw[QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal, Matrix.mul_diagonal,
      ite_eq_left hj0, mul_one, mul_one, embedMatrix_selDataInAct_apply,
      embedMatrix_selDataInAct_apply, hi0, hj0, ite_eq_left rfl, hiD, hjD] at hij
  exact hij
noncomputable def restrictMat {kData : ℕ} (A : Operator (2 ^ (kData + 18))) : Operator
    (2 ^ kData) := Matrix.of fun d' d ↦ A (liftPair0 (d', 0)) (liftPair0 (d, 0))
theorem op_mul_Pm_eq_embedMatrix_restrictMat {kData : ℕ} (A : Operator (2 ^ (kData + 18)))
    (hComm : A * (selMeasInAct kData).basisOutcomeProjector 0 = (selMeasInAct
    kData).basisOutcomeProjector 0 * A) : A * (selMeasInAct kData).basisOutcomeProjector 0 =
    (selDataInAct kData).embedMatrix (restrictMat A) *
    (selMeasInAct kData).basisOutcomeProjector 0 := by
  refine mul_basisOutcomeProjector_zero_eq_of_eq_on_zero (selMeasInAct kData) _ _ fun i j hj0 ↦ ?_
  rw [embedMatrix_selDataInAct_apply, hj0]
  by_cases hi0 : (selMeasInAct kData).extractIndex i = 0
  · rw [ite_eq_left hi0]; dsimp only [restrictMat]
    rw [Matrix.of_apply, liftPair0_zero_of_meas_zero hi0, liftPair0_zero_of_meas_zero hj0]
  · rw [ite_eq_right hi0]
    have hij := congrFun (congrFun hComm i) j
    rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul,
        ite_eq_left hj0, ite_eq_right hi0, mul_one, zero_mul] at hij
    exact hij
theorem restrictMat_mem_unitaryGroup_of_comm_Pm {kData : ℕ} (V : Unitary (2 ^ (kData + 18)))
    (hComm : V.1 * (selMeasInAct kData).basisOutcomeProjector 0 = (selMeasInAct
    kData).basisOutcomeProjector 0 * V.1) : restrictMat V.1 ∈ Matrix.unitaryGroup
    (Fin (2 ^ kData)) ℂ := by
  let selD := selDataInAct kData
  let selM := selMeasInAct kData
  let Pm := selM.basisOutcomeProjector 0
  let M := restrictMat V.1
  have hVPm : V.1 * Pm = selD.embedMatrix M * Pm := op_mul_Pm_eq_embedMatrix_restrictMat V.1 hComm
  have hPmH : Pmᴴ = Pm := QRegister.basisOutcomeProjector_conjTranspose selM 0
  have hPm2 : Pm * Pm = Pm := by
    ext i j
    simp only [Pm, QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal,
        Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; by_cases hz : selM.extractIndex i = 0 <;> simp [hz]
    · simp [hij]
  have hCommM : selD.embedMatrix M * Pm = Pm * selD.embedMatrix M :=
    (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint selD) selM
      (selDataInAct_disj_selMeasInAct kData) M 0
  have hV2 : V.1ᴴ * V.1 = 1 := by
    rw [← star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp V.2
  have hM2Pm : selD.embedMatrix (Mᴴ * M) * Pm = selD.embedMatrix 1 * Pm := by
    calc selD.embedMatrix (Mᴴ * M) * Pm
        = (selD.embedMatrix M)ᴴ * (selD.embedMatrix M * Pm) := by
            rw [QRegister.embedMatrix_mul, QRegister.embedMatrix_conjTranspose, Matrix.mul_assoc]
      _ = (selD.embedMatrix M)ᴴ * (Pm * (V.1 * Pm)) := by
            rw [← hVPm, ← Matrix.mul_assoc Pm V.1 Pm, ← hComm, Matrix.mul_assoc V.1 Pm Pm, hPm2]
      _ = (Pm * selD.embedMatrix M)ᴴ * (V.1 * Pm) := by
            rw [Matrix.conjTranspose_mul, hPmH, Matrix.mul_assoc]
      _ = (V.1 * Pm)ᴴ * (V.1 * Pm) := by rw [← hCommM, hVPm]
      _ = Pm * (V.1ᴴ * V.1) * Pm := by
        rw [Matrix.conjTranspose_mul, hPmH]; simp only [Matrix.mul_assoc]
      _ = selD.embedMatrix 1 * Pm := by
        rw [hV2, Matrix.mul_one, hPm2, QRegister.embedMatrix_one, Matrix.one_mul]
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]
  exact embedMatrix_selDataInAct_inj_on_Pm hM2Pm
/-- Restricted unitary on `Pm = (selMeasInAct kData).basisOutcomeProjector 0`. -/
noncomputable def restrictToMeasZero {kData : ℕ} (V : Unitary (2 ^ (kData + 18))) (hComm : V.1
    * (selMeasInAct kData).basisOutcomeProjector 0 = (selMeasInAct
    kData).basisOutcomeProjector 0 * V.1) : Unitary (2 ^ kData) :=
    ⟨restrictMat V.1, restrictMat_mem_unitaryGroup_of_comm_Pm V hComm⟩
theorem uLensSwap_conj_apply {kData : ℕ} (L : Slot18Lens kData)
    (A : Operator (2 ^ (kData + 18))) (i j : Fin (2 ^ (kData + 18))) :
    ((uLensSwap L).1 * A * (uLensSwap L).1) i j =
      A (lensSwapEquiv L i) (lensSwapEquiv L j) := by
  have hRight : ∀ (B : Operator (2 ^ (kData + 18))) (r c : Fin (2 ^ (kData + 18))),
      (B * (uLensSwap L).1) r c = B r (lensSwapEquiv L c) := fun B r c ↦ by
    rw [Matrix.mul_apply, Finset.sum_eq_single (lensSwapEquiv L c)]
    · dsimp only [uLensSwap]; rw [permUnitary_apply, ite_eq_left rfl, mul_one]
    · intro k _ hk; dsimp only [uLensSwap]; rw [permUnitary_apply, ite_eq_right hk, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hLeft : ∀ (r c : Fin (2 ^ (kData + 18))),
      ((uLensSwap L).1 * A) r c = A (lensSwapEquiv L r) c := fun r c ↦ by
    rw [Matrix.mul_apply, Finset.sum_eq_single (lensSwapEquiv L r)]
    · dsimp only [uLensSwap]
      rw [permUnitary_apply, ite_eq_left (lensSwapEquiv_involutive L r).symm, one_mul]
    · intro m _ hm; dsimp only [uLensSwap]
      rw [permUnitary_apply, ite_eq_right (fun hr ↦ hm (by rw [hr, lensSwapEquiv_involutive L m])),
          zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hRight ((uLensSwap L).1 * A) i j, hLeft i (lensSwapEquiv L j)]
/-- Active-slot zero projector `P_slot0 L` on `kData + 18` wires. -/
noncomputable def P_slot0 {kData : ℕ} (L : Slot18Lens kData) : Operator (2 ^ (kData + 18)) :=
  (uLensSwap L).1 * (selMeasInAct kData).basisOutcomeProjector 0 * (uLensSwap L).1
theorem P_slot0_eq_diagonal {kData : ℕ} (L : Slot18Lens kData) : P_slot0 L = Matrix.diagonal
    (fun xy ↦ if L.tbl ((selDataInAct kData).extractIndex xy) = 0 then (1 : ℂ) else 0) := by
  ext i j
  dsimp only [P_slot0]
  rw [uLensSwap_conj_apply, QRegister.basisOutcomeProjector_eq_diagonal]
  by_cases hij : i = j
  · subst hij
    have hM : (selMeasInAct kData).extractIndex (lensSwapEquiv L i) =
        L.tbl ((selDataInAct kData).extractIndex i) := by
      dsimp only [lensSwapEquiv]
      rw [Equiv.ofBijective_apply]
      exact (Prod.mk.inj (extractPair_liftPairIdx (lensSwapPerm L) i)).2
    simp only [Matrix.diagonal_apply_eq, hM]
  · rw [Matrix.diagonal_apply_ne _ (fun h ↦ hij ((lensSwapEquiv L).injective h)),
        Matrix.diagonal_apply_ne _ hij]
noncomputable def swapConjUnitary {kData : ℕ} (L : Slot18Lens kData)
    (uMid : Unitary (2 ^ (kData + 18))) : Unitary (2 ^ (kData + 18)) :=
  uLensSwap L * uMid * uLensSwap L
theorem swapConjUnitary_comm_Pm {kData : ℕ} (L : Slot18Lens kData)
    (uMid : Unitary (2 ^ (kData + 18))) (hCommSlot0 : uMid.1 * P_slot0 L = P_slot0 L * uMid.1)
    : (swapConjUnitary L uMid).1 * (selMeasInAct kData).basisOutcomeProjector 0 =
    (selMeasInAct kData).basisOutcomeProjector 0 * (swapConjUnitary L uMid).1 := by
  let S := (uLensSwap L).1
  let Pm := (selMeasInAct kData).basisOutcomeProjector 0
  have hS2 : S * S = 1 := uLensSwap_val_mul_self L
  change (S * uMid.1 * S) * Pm = Pm * (S * uMid.1 * S)
  change uMid.1 * (S * Pm * S) = (S * Pm * S) * uMid.1 at hCommSlot0
  calc (S * uMid.1 * S) * Pm
      = (S * uMid.1 * S * Pm) * (S * S) := by rw [hS2, Matrix.mul_one]
    _ = S * (uMid.1 * (S * Pm * S)) * S := by simp only [Matrix.mul_assoc]
    _ = S * ((S * Pm * S) * uMid.1) * S := by rw [hCommSlot0]
    _ = (S * S) * Pm * (S * uMid.1 * S) := by simp only [Matrix.mul_assoc]
    _ = Pm * (S * uMid.1 * S) := by rw [hS2, Matrix.one_mul]
/-- Restricted data unitary `restrictOfCommSlot0 L uMid hCommSlot0 : Unitary (2 ^ kData)`. -/
noncomputable def restrictOfCommSlot0 {kData : ℕ} (L : Slot18Lens kData)
    (uMid : Unitary (2 ^ (kData + 18))) (hCommSlot0 : uMid.1 * P_slot0 L = P_slot0 L * uMid.1)
    : Unitary (2 ^ kData) := restrictToMeasZero (swapConjUnitary L uMid)
    (swapConjUnitary_comm_Pm L uMid hCommSlot0)
theorem uMid_intertwines_uLensSwap_of_comm_P_slot0 {kData : ℕ} (L : Slot18Lens kData)
    (uMid : Unitary (2 ^ (kData + 18))) (hCommSlot0 : uMid.1 * P_slot0 L = P_slot0 L * uMid.1)
    : (uMid * uLensSwap L).1 * (selMeasInAct kData).basisOutcomeProjector 0 = (uLensSwap L).1
    * ((selDataInAct kData).embedUnitary (restrictOfCommSlot0 L uMid hCommSlot0)).1 *
    (selMeasInAct kData).basisOutcomeProjector 0 := by
  let Pm := (selMeasInAct kData).basisOutcomeProjector 0
  have hRes := op_mul_Pm_eq_embedMatrix_restrictMat (swapConjUnitary L uMid).1
    (swapConjUnitary_comm_Pm L uMid hCommSlot0)
  have hMul := congrArg ((uLensSwap L).1 * ·) hRes
  have hLhs : (uLensSwap L).1 * ((swapConjUnitary L uMid).1 * Pm) =
      (uMid * uLensSwap L).1 * Pm := by
    change (uLensSwap L).1 * (((uLensSwap L).1 * uMid.1 * (uLensSwap L).1) * Pm) =
      (uMid.1 * (uLensSwap L).1) * Pm
    calc (uLensSwap L).1 * (((uLensSwap L).1 * uMid.1 * (uLensSwap L).1) * Pm)
        = ((uLensSwap L).1 * (uLensSwap L).1) * (uMid.1 * (uLensSwap L).1) * Pm := by
          simp only [Matrix.mul_assoc]
      _ = (uMid.1 * (uLensSwap L).1) * Pm := by rw [uLensSwap_val_mul_self L, Matrix.one_mul]
  rw [hLhs, ← Matrix.mul_assoc] at hMul
  exact hMul
theorem extractIndex_compose_eq {n k₁ k₂ : ℕ}
    (r : QRegister k₂ n) (sel : QRegister k₁ k₂) (g : Fin (2 ^ n)) :
    sel.extractIndex (r.extractIndex g) = (r.compose sel).extractIndex g := by
  apply (basisBitsEquiv k₁).injective; funext i
  change basisBits k₁ (sel.extractIndex (r.extractIndex g)) i =
    basisBits k₁ ((r.compose sel).extractIndex g) i
  rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex,
      QRegister.basisBits_extractIndex, QRegister.compose_apply]
theorem replaceIndex_compose_eq {n k₁ k₂ : ℕ} (r : QRegister k₂ n) (sel : QRegister k₁ k₂)
    (g : Fin (2 ^ n)) (v : Fin (2 ^ k₁)) : r.replaceIndex g
    (sel.replaceIndex (r.extractIndex g) v) = (r.compose sel).replaceIndex g v := by
  apply (basisBitsEquiv n).injective; funext w
  change basisBits n (r.replaceIndex g (sel.replaceIndex (r.extractIndex g) v)) w =
    basisBits n ((r.compose sel).replaceIndex g v) w
  by_cases hw : w ∈ Set.range (r.compose sel).wires
  · obtain ⟨i, rfl⟩ := hw
    rw [QRegister.basisBits_replaceIndex_apply (r.compose sel) g v i, QRegister.compose_apply,
        QRegister.basisBits_replaceIndex_apply r g _ (sel i),
        QRegister.basisBits_replaceIndex_apply sel (r.extractIndex g) v i]
  · rw [QRegister.basisBits_replaceIndex_of_not_mem (r.compose sel) g v w hw]
    by_cases hwr : w ∈ Set.range r.wires
    · obtain ⟨u, rfl⟩ := hwr
      rw [QRegister.basisBits_replaceIndex_apply r g _ u,
          QRegister.basisBits_replaceIndex_of_not_mem sel (r.extractIndex g) v u
            (fun ⟨i, hi⟩ ↦ hw ⟨i, by dsimp [QRegister.compose]; rw [hi]⟩),
          QRegister.basisBits_extractIndex]
    · exact QRegister.basisBits_replaceIndex_of_not_mem r g _ w hwr
theorem embedMatrix_setTableOp_local {n kData : ℕ} (rData : QRegister kData n)
    (rMeas : QRegister 18 n) (hDM : rData.DisjointWires rMeas)
    (tbl : Fin (2 ^ kData) → Fin (2 ^ 18)) : (rData.concat rMeas hDM).embedMatrix
    (setTableOp (selDataInAct kData) (selMeasInAct kData) tbl) = setTableOp rData rMeas tbl
    := by
  let rAct := rData.concat rMeas hDM
  let selD := selDataInAct kData
  let selM := selMeasInAct kData
  have hD : rAct.compose selD = rData := concat_compose_selDataInAct rData rMeas hDM
  have hM : rAct.compose selM = rMeas := concat_compose_selMeasInAct rData rMeas hDM
  ext i g
  rw [QRegister.embedMatrix_apply]
  have hDg : selD.extractIndex (rAct.extractIndex g) = rData.extractIndex g :=
    (extractIndex_compose_eq rAct selD g).trans
      (congrArg (fun r : QRegister kData n ↦ r.extractIndex g) hD)
  let v := tbl (rData.extractIndex g)
  let zTarget := selM.replaceIndex (rAct.extractIndex g) v
  have hRepM : rAct.replaceIndex g zTarget = rMeas.replaceIndex g v :=
    (replaceIndex_compose_eq rAct selM g v).trans
      (congrArg (fun r : QRegister 18 n ↦ r.replaceIndex g v) hM)
  have hLHS : setTableOp selD selM tbl (rAct.extractIndex i) (rAct.extractIndex g) =
      if rAct.extractIndex i = zTarget then (1 : ℂ) else 0 := by
    unfold setTableOp; rw [Matrix.of_apply, hDg]
  have hRHS : setTableOp rData rMeas tbl i g =
      if i = rMeas.replaceIndex g v then (1 : ℂ) else 0 := by
    unfold setTableOp; rw [Matrix.of_apply]
  rw [hLHS, hRHS]
  by_cases henv : (rAct.basisSplitEquiv i).2 = (rAct.basisSplitEquiv g).2
  · rw [ite_eq_left henv, mul_one]
    have hiff : rAct.extractIndex i = zTarget ↔ i = rMeas.replaceIndex g v := by
      rw [← hRepM]
      constructor
      · intro hex
        exact rAct.basisSplitEquiv.injective (Prod.ext
          (by rw [QRegister.basisSplitEquiv_apply_fst, QRegister.basisSplitEquiv_apply_fst,
                  rAct.extractIndex_replaceIndex, hex])
          (by rw [henv, rAct.basisSplitEquiv_replaceIndex]))
      · rintro rfl; exact rAct.extractIndex_replaceIndex g zTarget
    by_cases h1 : rAct.extractIndex i = zTarget
    · rw [ite_eq_left h1, ite_eq_left (hiff.mp h1)]
    · rw [ite_eq_right h1, ite_eq_right (fun h2 ↦ h1 (hiff.mpr h2))]
  · rw [ite_eq_right henv, mul_zero]
    rw [ite_eq_right (fun hEq ↦ henv (by subst hEq; rw [← hRepM,
        rAct.basisSplitEquiv_replaceIndex]))]
/-- Active `18`-wire slot register on `kData` selected by `shiftedPartnerSlotFast`
(never forming `Fin (2 ^ posCoreWires)` so `omega` stays instantaneous). -/
def shiftedPartnerSlotReg {kData : ℕ} (selCore : QRegister posCoreWires kData)
    (d : Fin (2 ^ kData)) : QRegister 18 kData := selCore.compose (rElecSlot (QRegExt.ofFin
    posCoreWires) (shiftedPartnerSlotFast (fun w ↦ basisBits kData d (selCore w))))
private theorem elec3924_idx_lt (e : Fin 218) (j : Fin 18) : 18 * e.val + j.val < 3924 := by
  have := e.isLt; have := j.isLt; omega
private theorem add_one_lt_17 (a : Fin 8) : 1 + a.val < 17 := by
  have := a.isLt; omega
private theorem add_nine_lt_17 (b : Fin 8) : 9 + b.val < 17 := by
  have := b.isLt; omega
private theorem rElecSlot_apply_ofFin_local {m : ℕ} (rCore : QRegister posCoreWires m)
    (e : Fin 218) (j : Fin 18) :
    rElecSlot rCore e j = rCore (rElecSlot (QRegExt.ofFin posCoreWires) e j) := rfl
theorem shiftedPartnerSlotReg_replaceIndex {kData : ℕ}
    (selCore : QRegister posCoreWires kData) (d : Fin (2 ^ kData)) (v : Fin (2 ^ 18)) :
    shiftedPartnerSlotReg selCore ((shiftedPartnerSlotReg selCore d).replaceIndex d v) =
      shiftedPartnerSlotReg selCore d := by
  dsimp only [shiftedPartnerSlotReg]
  refine congrArg (fun s ↦ selCore.compose (rElecSlot (QRegExt.ofFin posCoreWires) s))
    (shiftedPartnerSlotFast_congr_outside fun w hwLo _ ↦ ?_)
  refine QRegister.basisBits_replaceIndex_of_not_mem _ d v (selCore w) ?_
  rintro ⟨j, hj⟩
  dsimp only [QRegister.compose_apply] at hj
  have hv := congrArg Fin.val (selCore.wires.injective hj)
  rw [rElecSlot_ofFin_val_local] at hv
  have hlt := elec3924_idx_lt (shiftedPartnerSlotFast (fun w' ↦ basisBits kData d (selCore w'))) j
  exact absurd (hv ▸ hlt) (Nat.not_lt.mpr (le_trans (by decide : 3924 ≤ 3949) hwLo))
/-- Polymorphic `Slot18Lens kData` for `shiftedPartnerSlotFast`. -/
noncomputable def shiftedPartnerLens218 {kData : ℕ}
    (selCore : QRegister posCoreWires kData) : Slot18Lens kData where
  tbl d := (shiftedPartnerSlotReg selCore d).extractIndex d
  updSlot d v := (shiftedPartnerSlotReg selCore d).replaceIndex d v
  get_put d v := by
    rw [shiftedPartnerSlotReg_replaceIndex, QRegister.extractIndex_replaceIndex]
  put_get d := QRegister.replaceIndex_extractIndex _ d
  put_put d v₁ v₂ := by
    rw [shiftedPartnerSlotReg_replaceIndex, QRegister.replaceIndex_replaceIndex]
theorem basisBits_shiftedPartnerLens218_tbl_eq {n kData : ℕ} (rData : QRegister kData n)
    (selCore : QRegister posCoreWires kData) (g : Fin (2 ^ n)) (j : Fin 18) : basisBits 18
    ((shiftedPartnerLens218 selCore).tbl (rData.extractIndex g)) j = basisBits n g (rElecSlot
    (rData.compose selCore) (shiftedPartnerSlotFast (fun w ↦ basisBits n g ((rData.compose
    selCore) w))) j) := by
  dsimp only [shiftedPartnerLens218]
  rw [QRegister.basisBits_extractIndex (shiftedPartnerSlotReg selCore (rData.extractIndex g))
      (rData.extractIndex g) j,
      QRegister.basisBits_extractIndex rData g]
  dsimp only [shiftedPartnerSlotReg, QRegister.compose_apply]
  rw [← QRegister.compose_apply rData selCore, ← rElecSlot_apply_ofFin_local (rData.compose
      selCore)]
  refine congrArg (fun s ↦ basisBits n g (rElecSlot (rData.compose selCore) s j))
    (shiftedPartnerSlotFast_congr_outside fun w _ _ ↦
      QRegister.basisBits_extractIndex rData g (selCore w))
/-- The `3,924`-wire electron subregister `[0 .. 3924)` inside `rCore : QRegister posCoreWires
  m`. -/
def rElec3924 {m : ℕ} (rCore : QRegister posCoreWires m) : QRegister 3924 m :=
  rCore.slice 0 3924 (by decide)
theorem rElecSlot_eq_rElec3924 {m : ℕ} (rCore : QRegister posCoreWires m)
    (e : Fin 218) (j : Fin 18) :
    rElecSlot rCore e j = rElec3924 rCore ⟨18 * e.val + j.val, by
      have := e.isLt; have := j.isLt; omega⟩ := by
  rw [rElecSlot_apply_ofFin_local]
  dsimp only [rElec3924, QRegister.slice_apply]
  refine congrArg rCore.wires (Fin.ext ?_)
  rw [rElecSlot_ofFin_val_local]; dsimp; omega
/-- Electron subregister `rElecInAct selCore : QRegister 3924 (kData + 18)`. -/
def rElecInAct {kData : ℕ} (selCore : QRegister posCoreWires kData) : QRegister 3924 (kData + 18) :=
  (selDataInAct kData).compose (rElec3924 selCore)
/-- Structural predicate certifying that `V : Unitary (2 ^ (kData + 18))` acts trivially on the
`3,924` electron wires `rElecInAct selCore`: it commutes with every single-qubit Hadamard `H`
on `rElecInAct selCore` and preserves all `3,924` electron bits in the computational basis. -/
def Elec3924Preserved {kData : ℕ} (selCore : QRegister posCoreWires kData)
    (V : Unitary (2 ^ (kData + 18))) : Prop := (∀ i : Fin 3924, (Circuit.H (rElecInAct selCore
    i)).eval * V = V * (Circuit.H (rElecInAct selCore i)).eval) ∧ (∀ (i : Fin 3924) (z' z :
    Fin (2 ^ (kData + 18))), V.1 z' z ≠ 0 → basisBits (kData + 18) z' (rElecInAct selCore i) =
    basisBits (kData + 18) z (rElecInAct selCore i))
private theorem unitary_comm_mul_local {d : ℕ} (A V₁ V₂ : Unitary d) (h₁ : A * V₁ = V₁ * A)
    (h₂ : A * V₂ = V₂ * A) : A * (V₁ * V₂) = (V₁ * V₂) * A := by
  apply Subtype.ext
  change A.1 * (V₁.1 * V₂.1) = (V₁.1 * V₂.1) * A.1
  have hi1 : A.1 * V₁.1 = V₁.1 * A.1 := congrArg Subtype.val h₁
  have hi2 : A.1 * V₂.1 = V₂.1 * A.1 := congrArg Subtype.val h₂
  rw [← Matrix.mul_assoc, hi1, Matrix.mul_assoc, hi2, ← Matrix.mul_assoc]
theorem elec3924Preserved_mul {kData : ℕ} (selCore : QRegister posCoreWires kData)
    {V₁ V₂ : Unitary (2 ^ (kData + 18))} (h₁ : Elec3924Preserved selCore V₁)
    (h₂ : Elec3924Preserved selCore V₂) : Elec3924Preserved selCore (V₁ * V₂) := by
  refine ⟨fun i ↦ unitary_comm_mul_local _ V₁ V₂ (h₁.1 i) (h₂.1 i), fun i z' z hnz ↦ ?_⟩
  rw [Submonoid.coe_mul, Matrix.mul_apply] at hnz
  obtain ⟨y, _, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
  exact (h₁.2 i z' y (left_ne_zero_of_mul hy)).trans (h₂.2 i y z (right_ne_zero_of_mul hy))
theorem elec3924Preserved_of_disjoint_embed {kData kSub : ℕ}
    (selCore : QRegister posCoreWires kData) (rSub : QRegister kSub (kData + 18))
    (hDisj : rSub.DisjointWires (rElecInAct selCore)) (W : Unitary (2 ^ kSub)) :
    Elec3924Preserved selCore (rSub.embedUnitary W) := by
  refine ⟨fun i ↦ ?_, fun i z' z hnz ↦ ?_⟩
  · have hDisj1 : (QRegister.singleton (rElecInAct selCore i)).DisjointWires rSub := by
      rw [QRegister.disjoint_iff]
      intro a b hab
      fin_cases a
      exact hDisj.ne b i hab.symm
    exact Subtype.ext (QRegister.embedMatrix_comm_of_disjoint (QRegister.singleton (rElecInAct
      selCore i)) rSub hDisj1 (PrimitiveGate.eval PrimitiveGate.H).1 W.1)
  · rw [QRegister.embedUnitary_val, QRegister.embedMatrix_apply] at hnz
    split_ifs at hnz with henv
    · exact ((rSub.basisSplit_environment_eq_iff z' z).mp henv) (rElecInAct selCore i)
        (fun ⟨j, hj⟩ ↦ hDisj.ne j i hj)
    · exact absurd (mul_zero _) hnz
theorem diagSignUnitary_mulVec_ket {N : ℕ} (p : Fin (2 ^ N) → Bool) (β : BitAssignment N) :
    (diagSignUnitary p).1.mulVec (ket β) =
      (if p ((basisBitsEquiv N).symm β) then (-1 : ℂ) else 1) • ket β := by
  let g := (basisBitsEquiv N).symm β
  rw [p2d_ket_eq_single β]
  ext i
  dsimp only [diagSignUnitary]
  rw [Matrix.mulVec_diagonal]
  by_cases hig : i = g <;> simp [hig, g]
private theorem comm_H_diagSignUnitary_of_indep_N {N : ℕ} (q : Wire N)
    (phase : Fin (2 ^ N) → Bool) (hIndep : ∀ z₁ z₂ : Fin (2 ^ N), (∀ w : Wire N, w ≠ q →
    basisBits N z₁ w = basisBits N z₂ w) → phase z₁ = phase z₂) : (Circuit.H q).eval *
    diagSignUnitary phase = diagSignUnitary phase * (Circuit.H q).eval := by
  apply Subtype.ext; apply matrix_ext_ket; intro α
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      diagSignUnitary_mulVec_ket, Matrix.mulVec_smul, ket_H q α,
      Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
      diagSignUnitary_mulVec_ket, diagSignUnitary_mulVec_ket]
  have h0 : basisBits N ((basisBitsEquiv N).symm (Function.update α q 0)) =
      Function.update α q 0 := (basisBitsEquiv N).apply_symm_apply _
  have h1 : basisBits N ((basisBitsEquiv N).symm (Function.update α q 1)) =
      Function.update α q 1 := (basisBitsEquiv N).apply_symm_apply _
  have hS : basisBits N ((basisBitsEquiv N).symm α) = α := (basisBitsEquiv N).apply_symm_apply _
  have hp0 : phase ((basisBitsEquiv N).symm (Function.update α q 0)) =
      phase ((basisBitsEquiv N).symm α) :=
    hIndep _ _ fun w hw ↦ by rw [h0, hS, Function.update_of_ne hw]
  have hp1 : phase ((basisBitsEquiv N).symm (Function.update α q 1)) =
      phase ((basisBitsEquiv N).symm α) :=
    hIndep _ _ fun w hw ↦ by rw [h1, hS, Function.update_of_ne hw]
  rw [hp0, hp1]
  by_cases hpa : phase ((basisBitsEquiv N).symm α) <;> simp [hpa, smul_add, smul_smul, mul_comm]
theorem elec3924Preserved_of_diagSignUnitary_indep {kData : ℕ}
    (selCore : QRegister posCoreWires kData) (phase : Fin (2 ^ (kData + 18)) → Bool) (hIndep :
    ∀ z₁ z₂ : Fin (2 ^ (kData + 18)), (∀ w : Wire (kData + 18), (∀ i : Fin 3924, w ≠
    rElecInAct selCore i) → basisBits (kData + 18) z₁ w = basisBits (kData + 18) z₂ w) → phase
    z₁ = phase z₂) : Elec3924Preserved selCore (diagSignUnitary phase) := by
  refine ⟨fun i ↦ comm_H_diagSignUnitary_of_indep_N (rElecInAct selCore i) phase (fun z₁ z₂ h
    ↦ hIndep z₁ z₂ fun w hw ↦ h w (hw i)), fun i z' z hnz ↦ ?_⟩
  dsimp only [diagSignUnitary] at hnz
  by_cases hz : z' = z
  · rw [hz]
  · exact absurd (Matrix.diagonal_apply_ne _ hz) hnz
/-- `comm_P_slot0_of_elec3924Preserved`: any `uMid` satisfying `Elec3924Preserved selCore uMid`
and `ActPreservesShifted17 selCore uMid` automatically commutes with `P_slot0
(shiftedPartnerLens218 selCore)`! -/
theorem comm_P_slot0_of_elec3924Preserved {kData : ℕ} (selCore : QRegister posCoreWires kData)
    (uMid : Unitary (2 ^ (kData + 18))) (hElec : Elec3924Preserved selCore uMid)
    (hPres17 : ActPreservesShifted17 selCore uMid) : uMid.1 * P_slot0
    (shiftedPartnerLens218 selCore) = P_slot0 (shiftedPartnerLens218 selCore) * uMid.1 := by
  let L := shiftedPartnerLens218 selCore
  ext z' z
  rw [P_slot0_eq_diagonal L, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hnz : uMid.1 z' z = 0
  · simp [hnz]
  · have hTblEq : L.tbl ((selDataInAct kData).extractIndex z') =
        L.tbl ((selDataInAct kData).extractIndex z) := by
      have h17 := hPres17 z z' hnz
      have h17Bits : ∀ idx : Fin 17,
          basisBits kData ((selDataInAct kData).extractIndex z') (selCore (rShiftedIdx17OfFin idx))
              =
          basisBits kData ((selDataInAct kData).extractIndex z) (selCore (rShiftedIdx17OfFin idx))
              :=
        fun idx ↦ by
          have h := congrFun (congrArg (basisBits 17) h17) idx
          simpa only [selShiftedIdx17, QRegister.basisBits_extractIndex, QRegister.compose_apply]
              using h
      have hSlotEq : shiftedPartnerSlotFast (fun w ↦ basisBits kData ((selDataInAct
          kData).extractIndex z') (selCore w)) =
          shiftedPartnerSlotFast (fun w ↦ basisBits kData ((selDataInAct kData).extractIndex z)
              (selCore w)) := by
        refine shiftedPartnerSlotFast_congr ?_ (fun a ↦ ?_) (fun b ↦ ?_)
        · have h0 := h17Bits ⟨0, by decide⟩
          rwa [rShiftedIdx17OfFin_zero] at h0
        · have ha := h17Bits ⟨1 + a.val, add_one_lt_17 a⟩
          rwa [rShiftedIdx17OfFin_anc a] at ha
        · have hb := h17Bits ⟨9 + b.val, add_nine_lt_17 b⟩
          rwa [rShiftedIdx17OfFin_part b] at hb
      let d' := (selDataInAct kData).extractIndex z'
      let d := (selDataInAct kData).extractIndex z
      dsimp only [L, shiftedPartnerLens218]
      refine basisBits_inj fun j ↦ ?_
      rw [QRegister.basisBits_extractIndex (shiftedPartnerSlotReg selCore d') d' j,
          QRegister.basisBits_extractIndex (shiftedPartnerSlotReg selCore d) d j]
      dsimp only [shiftedPartnerSlotReg]
      rw [hSlotEq]
      let s₀ := shiftedPartnerSlotFast (fun w ↦ basisBits kData ((selDataInAct kData).extractIndex
          z) (selCore w))
      have hWire : ∀ w : Fin (2 ^ (kData + 18)),
          basisBits kData ((selDataInAct kData).extractIndex w)
            ((selCore.compose (rElecSlot (QRegExt.ofFin posCoreWires) s₀)) j) =
          basisBits (kData + 18) w (rElecInAct selCore ⟨18 * s₀.val + j.val, elec3924_idx_lt s₀ j⟩)
              := fun w ↦ by
        rw [QRegister.basisBits_extractIndex (selDataInAct kData) w
              ((selCore.compose (rElecSlot (QRegExt.ofFin posCoreWires) s₀)) j)]
        refine congrArg (basisBits (kData + 18) w) ?_
        dsimp only [rElecInAct, QRegister.compose_apply]
        congr 1
        rw [← rElecSlot_apply_ofFin_local selCore, rElecSlot_eq_rElec3924 selCore s₀ j]
      rw [hWire z', hWire z]
      exact hElec.2 _ z' z hnz
    rw [hTblEq]
    by_cases h0 : L.tbl ((selDataInAct kData).extractIndex z) = 0 <;> simp [h0]
-- ============================================================================
-- Section 3A: Hadamard Walls (`cHadReg`), Phase-Kick Prefix (`uKickPrefix218`),
--             & Load / Electron-Only Hadamard Write Conjugation
-- ============================================================================
theorem ite_decide_eq_one_zmod2 (x : ZMod 2) :
    (if decide (x = 1) = true then (-1 : ℂ) else 1) = (-1 : ℂ) ^ x.val := by
  rcases bit_cases x with rfl | rfl <;> norm_num
private theorem permUnitary_apply_local {d : ℕ} (σ : Equiv.Perm (Fin d)) (i j : Fin d) :
    (Operator.permutationUnitary σ).1 i j = if σ j = i then 1 else 0 := by
  dsimp [Operator.permutationUnitary]
  by_cases h : σ j = i
  · subst h; simp
  · have h' : σ.symm i ≠ j := fun heq ↦ h (by rw [← heq, σ.apply_symm_apply])
    simp [h, h']
theorem sqrtHalf_sq_mul_two : (sqrtHalf * sqrtHalf : ℂ) * 2 = 1 := by
  rw [sqrtHalf_mul_sqrtHalf]; ring
theorem eval_H_mul_self {k : ℕ} (w : Wire k) :
    (Circuit.H w).eval * (Circuit.H w).eval = 1 := by
  change (Circuit.H w ;;ᶜ Circuit.H w).eval = 1
  apply Subtype.ext; apply matrix_ext_ket; intro β
  have hsqrt := sqrtHalf_sq_mul_two
  let g0 := Function.update β w 0
  let g1 := Function.update β w 1
  have hg0w : g0 w = 0 := Function.update_self _ _ _
  have hg1w : g1 w = 1 := Function.update_self _ _ _
  have hg00 : Function.update g0 w 0 = g0 := Function.update_idem _ _ _
  have hg01 : Function.update g0 w 1 = g1 := Function.update_idem _ _ _
  have hg10 : Function.update g1 w 0 = g0 := Function.update_idem _ _ _
  have hg11 : Function.update g1 w 1 = g1 := Function.update_idem _ _ _
  rw [eval_seq_mulVec, ket_H w β]
  change (Circuit.H w).eval.1.mulVec (sqrtHalf • (ket g0 + bitSign (β w) • ket g1)) =
    (1 : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ).mulVec (ket β)
  rw [Matrix.one_mulVec, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
      ket_H w g0, ket_H w g1, hg0w, hg1w, hg00, hg01, hg10, hg11]
  rcases bit_cases (β w) with hw | hw
  · have hb_eq : g0 = β := by dsimp [g0]; rw [← hw, Function.update_eq_self]
    ext idx
    simp only [hw, bitSign, one_ne_zero, ↓reduceIte, hb_eq,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (ket β idx) * hsqrt
  · have hb_eq : g1 = β := by dsimp [g1]; rw [← hw, Function.update_eq_self]
    ext idx
    simp only [hw, bitSign, one_ne_zero, ↓reduceIte, hb_eq,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (ket β idx) * hsqrt
theorem eval_H_comm {k : ℕ} (a b : Wire k) (hne : a ≠ b) :
    (Circuit.H a).eval * (Circuit.H b).eval = (Circuit.H b).eval * (Circuit.H a).eval := by
  change (Circuit.H b ;;ᶜ Circuit.H a).eval = (Circuit.H a ;;ᶜ Circuit.H b).eval
  apply Subtype.ext; apply matrix_ext_ket; intro β
  simp only [eval_seq_mulVec, ket_H, Matrix.mulVec_smul, Matrix.mulVec_add,
    Function.update_of_ne hne, Function.update_of_ne hne.symm, Function.update_comm hne]
  ext idx
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
/-- Hadamard wall on the first `k` wires of `r : QRegister K n` (`0 T`, `TOFF = 0`). -/
def cHadRegAux {n K : ℕ} (r : QRegister K n) : ∀ (k : ℕ), k ≤ K → Circuit n
  | 0, _ => .identity
  | k + 1, hk => cHadRegAux r k (by omega) ;;ᶜ Circuit.H (r ⟨k, hk⟩)
/-- Hadamard wall on all `K` wires of `r : QRegister K n` (`0 T`, `TOFF = 0`). -/
def cHadReg {n K : ℕ} (r : QRegister K n) : Circuit n := cHadRegAux r K le_rfl
theorem cHadRegAux_count_toff {n K : ℕ} (r : QRegister K n) :
    ∀ (k : ℕ) (hk : k ≤ K), (cHadRegAux r k hk).count TOFF = 0
  | 0, _ => rfl
  | k + 1, hk => by
      dsimp only [cHadRegAux]
      rw [Circuit.count_seq, cHadRegAux_count_toff r k (by omega)]
      rfl
theorem cHadReg_count_toff {n K : ℕ} (r : QRegister K n) : (cHadReg r).count TOFF = 0 :=
    cHadRegAux_count_toff r K le_rfl
theorem cHadRegAux_count_t {n K : ℕ} (r : QRegister K n) :
    ∀ (k : ℕ) (hk : k ≤ K), (cHadRegAux r k hk).count T = 0
  | 0, _ => rfl
  | k + 1, hk => by
      dsimp only [cHadRegAux]
      rw [Circuit.count_seq, cHadRegAux_count_t r k (by omega)]
      rfl
theorem cHadReg_count_t {n K : ℕ} (r : QRegister K n) : (cHadReg r).count T = 0 :=
    cHadRegAux_count_t r K le_rfl
theorem cHadRegAux_comm_H {n K : ℕ} (r : QRegister K n) (q : Wire n) :
    ∀ (k : ℕ) (hk : k ≤ K),
      (∀ i : Fin k, r ⟨i.val, by omega⟩ ≠ q) →
      (cHadRegAux r k hk).eval * (Circuit.H q).eval =
        (Circuit.H q).eval * (cHadRegAux r k hk).eval
  | 0, _, _ => by
      change 1 * (Circuit.H q).eval = (Circuit.H q).eval * 1
      rw [one_mul, mul_one]
  | k + 1, hk, hne => by
      have ih := cHadRegAux_comm_H r q k (by omega) (fun i ↦ hne ⟨i.val, by omega⟩)
      have hlast : r ⟨k, hk⟩ ≠ q := hne ⟨k, Nat.lt_succ_self k⟩
      change ((Circuit.H (r ⟨k, hk⟩)).eval * (cHadRegAux r k (by omega)).eval) * (Circuit.H q).eval
          =
        (Circuit.H q).eval * ((Circuit.H (r ⟨k, hk⟩)).eval * (cHadRegAux r k (by omega)).eval)
      rw [mul_assoc, ih, ← mul_assoc, eval_H_comm _ _ hlast, mul_assoc]
theorem cHadRegAux_eval_mul_self {n K : ℕ} (r : QRegister K n) :
    ∀ (k : ℕ) (hk : k ≤ K),
      (cHadRegAux r k hk).eval * (cHadRegAux r k hk).eval = 1
  | 0, _ => mul_one 1
  | k + 1, hk => by
      have ih := cHadRegAux_eval_mul_self r k (by omega)
      have hcomm := cHadRegAux_comm_H r (r ⟨k, hk⟩) k (by omega)
        (fun i ↦ r.wires.injective.ne (Fin.ne_of_val_ne (by dsimp; omega)))
      change ((Circuit.H (r ⟨k, hk⟩)).eval * (cHadRegAux r k (by omega)).eval) *
          ((Circuit.H (r ⟨k, hk⟩)).eval * (cHadRegAux r k (by omega)).eval) = 1
      calc
        ((Circuit.H (r ⟨k, hk⟩)).eval * (cHadRegAux r k (by omega)).eval) *
            ((Circuit.H (r ⟨k, hk⟩)).eval * (cHadRegAux r k (by omega)).eval)
          = (Circuit.H (r ⟨k, hk⟩)).eval *
              ((cHadRegAux r k (by omega)).eval * (Circuit.H (r ⟨k, hk⟩)).eval) *
              (cHadRegAux r k (by omega)).eval := by simp only [mul_assoc]
        _ = ((Circuit.H (r ⟨k, hk⟩)).eval * (Circuit.H (r ⟨k, hk⟩)).eval) *
              ((cHadRegAux r k (by omega)).eval * (cHadRegAux r k (by omega)).eval) := by
              rw [hcomm]; simp only [mul_assoc]
        _ = 1 := by rw [eval_H_mul_self, ih, one_mul]
theorem cHadReg_eval_mul_self {n K : ℕ} (r : QRegister K n) : (cHadReg r).eval *
    (cHadReg r).eval = 1 := cHadRegAux_eval_mul_self r K le_rfl
theorem singleHad_conj_phase_ket {n : ℕ} (q : Wire n)
    (b : BitAssignment n → ZMod 2)
    (hb : ∀ α₁ α₂ : BitAssignment n, (∀ w, w ≠ q → α₁ w = α₂ w) → b α₁ = b α₂)
    (α : BitAssignment n) :
    let U₁ : Unitary (2 ^ n) :=
      diagSignUnitary (fun g ↦ decide (b (basisBits n g) * basisBits n g q = 1))
    ((Circuit.H q).eval * U₁ * (Circuit.H q).eval).1.mulVec (ket α) =
      ket (Function.update α q (α q + b α)) := by
  intro U₁
  have hb0 : b (Function.update α q 0) = b α := hb _ _ fun w hw ↦ Function.update_of_ne hw _ _
  have hb1 : b (Function.update α q 1) = b α := hb _ _ fun w hw ↦ Function.update_of_ne hw _ _
  have hMid : U₁.1.mulVec ((Circuit.H q).eval.1.mulVec (ket α)) =
      (Circuit.H q).eval.1.mulVec (ket (Function.update α q (α q + b α))) := by
    rw [ket_H q α, ket_H q (Function.update α q (α q + b α)),
        Function.update_idem, Function.update_idem, Function.update_self,
        Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul]
    dsimp only [U₁]
    rw [diagSignUnitary_mulVec_ket, diagSignUnitary_mulVec_ket]
    have hEq0 : basisBits n ((basisBitsEquiv n).symm (Function.update α q 0)) =
        Function.update α q 0 := (basisBitsEquiv n).apply_symm_apply _
    have hEq1 : basisBits n ((basisBitsEquiv n).symm (Function.update α q 1)) =
        Function.update α q 1 := (basisBitsEquiv n).apply_symm_apply _
    simp only [hEq0, hEq1, hb0, hb1, Function.update_self, mul_zero, mul_one]
    rcases bit_cases (α q) with hq | hq <;> rcases bit_cases (b α) with hba | hba <;>
      simp [hq, hba, bitSign]
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hMid, Matrix.mulVec_mulVec]
  have hHH : (Circuit.H q).eval.1 * (Circuit.H q).eval.1 = 1 :=
    congrArg Subtype.val (eval_H_mul_self q)
  rw [hHH, Matrix.one_mulVec]
theorem comm_H_diagSignUnitary_of_ignores {n : ℕ} (q : Wire n) (p : BitAssignment n → Bool)
    (hp : ∀ α₁ α₂ : BitAssignment n, (∀ w, w ≠ q → α₁ w = α₂ w) → p α₁ = p α₂) :
    (Circuit.H q).eval * diagSignUnitary (fun g ↦ p (basisBits n g)) = diagSignUnitary
    (fun g ↦ p (basisBits n g)) * (Circuit.H q).eval := by
  apply Subtype.ext; apply matrix_ext_ket; intro α
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      diagSignUnitary_mulVec_ket, Matrix.mulVec_smul, ket_H q α,
      Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
      diagSignUnitary_mulVec_ket, diagSignUnitary_mulVec_ket]
  have hS : basisBits n ((basisBitsEquiv n).symm α) = α := (basisBitsEquiv n).apply_symm_apply _
  have h0 : basisBits n ((basisBitsEquiv n).symm (Function.update α q 0)) =
      Function.update α q 0 := (basisBitsEquiv n).apply_symm_apply _
  have h1 : basisBits n ((basisBitsEquiv n).symm (Function.update α q 1)) =
      Function.update α q 1 := (basisBitsEquiv n).apply_symm_apply _
  rw [hS, h0, h1, hp (Function.update α q 0) α (fun w hw ↦ Function.update_of_ne hw 0 α),
      hp (Function.update α q 1) α (fun w hw ↦ Function.update_of_ne hw 1 α)]
  by_cases hpa : p α <;> simp [hpa, smul_add, smul_smul, mul_comm]
theorem cHadRegAux_comm_diagSignUnitary {n K : ℕ} (r : QRegister K n)
    (p : BitAssignment n → Bool) :
    ∀ (k : ℕ) (hk : k ≤ K),
      (∀ (i : Fin k) (α₁ α₂ : BitAssignment n),
        (∀ w, w ≠ r ⟨i.val, by omega⟩ → α₁ w = α₂ w) → p α₁ = p α₂) →
      (cHadRegAux r k hk).eval * diagSignUnitary (fun g ↦ p (basisBits n g)) =
        diagSignUnitary (fun g ↦ p (basisBits n g)) * (cHadRegAux r k hk).eval := by
  intro k
  induction k with
  | zero =>
      intro _ _
      change 1 * _ = _ * 1
      rw [one_mul, mul_one]
  | succ k ih =>
      intro hk hp
      have ihStep := ih (by omega) fun i α₁ α₂ h ↦ hp ⟨i.val, by omega⟩ α₁ α₂ h
      have hlast := comm_H_diagSignUnitary_of_ignores (r ⟨k, hk⟩) p (hp ⟨k, Nat.lt_succ_self k⟩)
      change ((Circuit.H (r ⟨k, hk⟩)).eval * (cHadRegAux r k (by omega)).eval) * _ =
        _ * ((Circuit.H (r ⟨k, hk⟩)).eval * (cHadRegAux r k (by omega)).eval)
      rw [mul_assoc, ihStep, ← mul_assoc, hlast, mul_assoc]
theorem cHadRegAux_conj_phase_ket {n K : ℕ} (r : QRegister K n)
    (b : Fin K → BitAssignment n → ZMod 2)
    (hb : ∀ (i : Fin K) (α₁ α₂ : BitAssignment n),
      (∀ w, (∀ t : Fin K, w ≠ r t) → α₁ w = α₂ w) → b i α₁ = b i α₂) :
    ∀ (k : ℕ) (hk : k ≤ K) (β : BitAssignment n),
      ((cHadRegAux r k hk).eval *
        diagSignUnitary (fun g ↦
          decide ((∑ i : Fin k, b ⟨i.val, by omega⟩ (basisBits n g) *
            basisBits n g (r ⟨i.val, by omega⟩)) = 1)) *
        (cHadRegAux r k hk).eval).1.mulVec (ket β) =
        ket (fun w ↦ if h : ∃ i : Fin k, w = r ⟨i.val, by omega⟩ then
          β w + b ⟨h.choose.val, by omega⟩ β else β w) := by
  intro k
  induction k with
  | zero =>
      intro hk β
      let U_pref : Unitary (2 ^ n) := diagSignUnitary fun g ↦
        decide ((∑ i : Fin 0, b ⟨i.val, by omega⟩ (basisBits n g) *
          basisBits n g (r ⟨i.val, by omega⟩)) = 1)
      have hU0 : U_pref = 1 := by
        apply Subtype.ext; apply matrix_ext_ket; intro α
        rw [diagSignUnitary_mulVec_ket, OneMemClass.coe_one, Matrix.one_mulVec]
        simp
      change ((1 : Unitary (2 ^ n)) * U_pref * 1).1.mulVec (ket β) = _
      rw [hU0, mul_one, mul_one, OneMemClass.coe_one, Matrix.one_mulVec]
      simp
  | succ k ih =>
      intro hk β
      let U_pref : Unitary (2 ^ n) := diagSignUnitary fun g ↦
        decide ((∑ i : Fin (k + 1), b ⟨i.val, by omega⟩ (basisBits n g) *
          basisBits n g (r ⟨i.val, by omega⟩)) = 1)
      let q := r ⟨k, hk⟩
      let p_prev : BitAssignment n → Bool := fun α ↦
        decide ((∑ i : Fin k, b ⟨i.val, by omega⟩ α * α (r ⟨i.val, by omega⟩)) = 1)
      let p_one : BitAssignment n → Bool := fun α ↦ decide (b ⟨k, hk⟩ α * α q = 1)
      let U_prev : Unitary (2 ^ n) := diagSignUnitary fun g ↦ p_prev (basisBits n g)
      let U_one : Unitary (2 ^ n) := diagSignUnitary fun g ↦ p_one (basisBits n g)
      have hU_split : U_pref = U_one * U_prev := by
        apply Subtype.ext; apply matrix_ext_ket; intro α
        rw [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
        dsimp only [U_pref, U_prev, U_one, p_prev, p_one]
        rw [diagSignUnitary_mulVec_ket, diagSignUnitary_mulVec_ket,
            Matrix.mulVec_smul, diagSignUnitary_mulVec_ket, smul_smul]
        have hα : basisBits n ((basisBitsEquiv n).symm α) = α :=
          (basisBitsEquiv n).apply_symm_apply _
        simp only [hα, ite_decide_eq_one_zmod2]
        refine congrArg (· • ket α) ?_
        rw [Fin.sum_univ_castSucc]
        dsimp only [Fin.val_castSucc, Fin.val_last]
        rw [← TempPhaseProg.neg_one_pow_zmod2_mul, mul_comm]
      have hCommH_Had : (cHadRegAux r k (by omega)).eval * (Circuit.H q).eval =
          (Circuit.H q).eval * (cHadRegAux r k (by omega)).eval :=
        cHadRegAux_comm_H r q k (by omega)
          (fun i ↦ r.wires.injective.ne (Fin.ne_of_val_ne (by dsimp; omega)))
      have hCommH_Prev : (Circuit.H q).eval * U_prev = U_prev * (Circuit.H q).eval :=
        comm_H_diagSignUnitary_of_ignores q p_prev fun α₁ α₂ h ↦ by
          dsimp only [p_prev]
          congr 1; congr 1; refine Finset.sum_congr rfl fun i _ ↦ ?_
          have hri : r ⟨i.val, by omega⟩ ≠ q :=
            r.wires.injective.ne (Fin.ne_of_val_ne (by dsimp; omega))
          rw [h _ hri, hb ⟨i.val, by omega⟩ α₁ α₂ (fun w hw ↦ h w (hw ⟨k, hk⟩))]
      have hCommHad_One : (cHadRegAux r k (by omega)).eval * U_one =
          U_one * (cHadRegAux r k (by omega)).eval :=
        cHadRegAux_comm_diagSignUnitary r p_one k (by omega) fun i α₁ α₂ h ↦ by
          dsimp only [p_one]
          have hqi : q ≠ r ⟨i.val, by omega⟩ :=
            r.wires.injective.ne (Fin.ne_of_val_ne (by dsimp; omega))
          rw [h q hqi, hb ⟨k, hk⟩ α₁ α₂ (fun w hw ↦ h w (hw ⟨i.val, by omega⟩))]
      have hFactor : (cHadRegAux r (k + 1) hk).eval * U_pref * (cHadRegAux r (k + 1) hk).eval
          = ((Circuit.H q).eval * U_one * (Circuit.H q).eval) * ((cHadRegAux r k
          (by omega)).eval * U_prev * (cHadRegAux r k (by omega)).eval) := by
        change ((Circuit.H q).eval * (cHadRegAux r k (by omega)).eval) * U_pref *
            ((Circuit.H q).eval * (cHadRegAux r k (by omega)).eval) = _
        rw [hU_split]
        calc
          ((Circuit.H q).eval * (cHadRegAux r k (by omega)).eval) * (U_one * U_prev) *
              ((Circuit.H q).eval * (cHadRegAux r k (by omega)).eval)
            = (Circuit.H q).eval * ((cHadRegAux r k (by omega)).eval * U_one) *
                U_prev * ((Circuit.H q).eval * (cHadRegAux r k (by omega)).eval) := by
                simp only [mul_assoc]
          _ = (Circuit.H q).eval * U_one * (cHadRegAux r k (by omega)).eval *
                (U_prev * (Circuit.H q).eval) * (cHadRegAux r k (by omega)).eval := by
                rw [hCommHad_One]; simp only [mul_assoc]
          _ = (Circuit.H q).eval * U_one *
                ((cHadRegAux r k (by omega)).eval * (Circuit.H q).eval) * U_prev *
                (cHadRegAux r k (by omega)).eval := by
                rw [← hCommH_Prev]; simp only [mul_assoc]
          _ = ((Circuit.H q).eval * U_one * (Circuit.H q).eval) *
                ((cHadRegAux r k (by omega)).eval * U_prev * (cHadRegAux r k (by omega)).eval) := by
                rw [hCommH_Had]; simp only [mul_assoc]
      let β_prev : BitAssignment n := fun w ↦
        if h : ∃ i : Fin k, w = r ⟨i.val, by omega⟩ then
          β w + b ⟨h.choose.val, by omega⟩ β else β w
      have ihStep : ((cHadRegAux r k (by omega)).eval * U_prev *
          (cHadRegAux r k (by omega)).eval).1.mulVec (ket β) = ket β_prev := ih (by omega) β
      change ((cHadRegAux r (k + 1) hk).eval * U_pref *
        (cHadRegAux r (k + 1) hk).eval).1.mulVec (ket β) = _
      rw [hFactor, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ihStep,
          singleHad_conj_phase_ket q (b ⟨k, hk⟩) (fun α₁ α₂ h ↦ hb ⟨k, hk⟩ α₁ α₂ fun w hw ↦ h w (hw
              ⟨k, hk⟩)) β_prev]
      refine congrArg ket (funext fun w ↦ ?_)
      have hb_prev : b ⟨k, hk⟩ β_prev = b ⟨k, hk⟩ β :=
        hb ⟨k, hk⟩ β_prev β fun w' hw' ↦ dite_eq_right (fun ⟨i, hi⟩ ↦ hw' ⟨i.val, by omega⟩ hi)
      by_cases hwq : w = q
      · subst hwq
        rw [Function.update_self, hb_prev]
        have hnotPrev : ¬ ∃ i : Fin k, q = r ⟨i.val, by omega⟩ := fun ⟨i, hi⟩ ↦
          r.wires.injective.ne (Fin.ne_of_val_ne (by dsimp; omega)) hi.symm
        have hPrevQ : β_prev q = β q := dite_eq_right hnotPrev
        have hexSucc : ∃ i : Fin (k + 1), q = r ⟨i.val, by omega⟩ := ⟨⟨k, Nat.lt_succ_self k⟩, rfl⟩
        rw [hPrevQ, dite_eq_left hexSucc]
        have hch : hexSucc.choose.val = k := by
          have := r.wires.injective hexSucc.choose_spec
          exact (congrArg Fin.val this).symm
        exact congrArg (fun idx ↦ β q + b idx β) (Fin.ext (by dsimp; omega))
      · rw [Function.update_of_ne hwq]
        by_cases hex : ∃ i : Fin k, w = r ⟨i.val, by omega⟩
        · obtain ⟨i₀, hi₀⟩ := hex
          have hex1 : ∃ i : Fin (k + 1), w = r ⟨i.val, by omega⟩ := ⟨⟨i₀.val, by omega⟩, hi₀⟩
          dsimp only [β_prev]
          rw [dite_eq_left ⟨i₀, hi₀⟩, dite_eq_left hex1]
          have hch0 : (Exists.choose (⟨i₀, hi₀⟩ : ∃ i : Fin k, w = r ⟨i.val, by omega⟩)).val =
              i₀.val := by
            have := r.wires.injective ((Exists.choose_spec (⟨i₀, hi₀⟩ : ∃ i : Fin k, w = r ⟨i.val,
                by omega⟩)).symm.trans hi₀)
            exact congrArg (Fin.val : Fin K → ℕ) this
          have hch1 : hex1.choose.val = i₀.val := by
            have := r.wires.injective (hex1.choose_spec.symm.trans hi₀)
            exact congrArg (Fin.val : Fin K → ℕ) this
          exact congrArg (fun idx ↦ β w + b idx β) (Fin.ext (by dsimp; omega))
        · have hex1 : ¬ ∃ i : Fin (k + 1), w = r ⟨i.val, by omega⟩ := fun ⟨i, hi⟩ ↦ by
            by_cases hik : i.val = k
            · exact hwq (hi.trans (congrArg r.wires (Fin.ext (by dsimp; omega))))
            · exact hex ⟨⟨i.val, by omega⟩, hi⟩
          dsimp only [β_prev]
          rw [dite_eq_right hex, dite_eq_right hex1]
theorem cHadReg_conj_phase_ket {n K : ℕ} (r : QRegister K n)
    (b : Fin K → BitAssignment n → ZMod 2) (hb : ∀ (i : Fin K) (α₁ α₂ : BitAssignment n), (∀
    w, (∀ t : Fin K, w ≠ r t) → α₁ w = α₂ w) → b i α₁ = b i α₂) (β : BitAssignment n) :
    ((cHadReg r).eval * diagSignUnitary (fun g ↦ decide ((∑ i : Fin K, b i (basisBits n g) *
    basisBits n g (r i)) = 1)) * (cHadReg r).eval).1 *ᵥ ket β = ket
    (p2d_writeReg β r (fun i ↦ β (r i) + b i β)) := by
  have hAux := cHadRegAux_conj_phase_ket r b hb K le_rfl β
  have hUEq : (diagSignUnitary fun g : Fin (2 ^ n) ↦
      decide ((∑ i : Fin K, b ⟨i.val, by omega⟩ (basisBits n g) *
        basisBits n g (r ⟨i.val, by omega⟩)) = 1)) =
      diagSignUnitary (fun g ↦
        decide ((∑ i : Fin K, b i (basisBits n g) * basisBits n g (r i)) = 1)) :=
    congrArg diagSignUnitary (funext fun _ ↦ rfl)
  rw [hUEq] at hAux
  dsimp only [cHadReg]
  rw [hAux]
  refine congrArg ket (funext fun w ↦ ?_)
  by_cases hw : w ∈ Set.range r.wires
  · obtain ⟨i₀, rfl⟩ := hw
    have hex : ∃ i : Fin K, r i₀ = r ⟨i.val, by omega⟩ := ⟨i₀, rfl⟩
    rw [dite_eq_left hex, p2d_writeReg_apply_reg]
    have hch : (⟨hex.choose.val, by omega⟩ : Fin K) = i₀ :=
      r.wires.injective hex.choose_spec.symm
    rw [hch]
  · have hnot : ¬ ∃ i : Fin K, w = r ⟨i.val, by omega⟩ :=
      fun ⟨i, hi⟩ ↦ hw ⟨⟨i.val, by omega⟩, hi.symm⟩
    rw [dite_eq_right hnot, p2d_writeReg_apply_of_not_mem _ _ _ _ hw]
theorem cHadRegAux_preserves_ketPredProj {n K : ℕ} (r : QRegister K n)
    (S : BitAssignment n → Prop)
    (hS : ∀ β₁ β₂ : BitAssignment n,
      (∀ w, (∀ t : Fin K, w ≠ r t) → β₁ w = β₂ w) → (S β₁ ↔ S β₂)) :
    ∀ (k : ℕ) (hk : k ≤ K),
      p2d_ketPredProj S * (cHadRegAux r k hk).eval.1 =
        (cHadRegAux r k hk).eval.1 * p2d_ketPredProj S
  | 0, _ => by
      change p2d_ketPredProj S * 1 = 1 * p2d_ketPredProj S
      rw [mul_one, one_mul]
  | k + 1, hk => by
      classical
      have ih := cHadRegAux_preserves_ketPredProj r S hS k (by omega)
      have hH : p2d_ketPredProj S * (Circuit.H (r ⟨k, hk⟩)).eval.1 =
          (Circuit.H (r ⟨k, hk⟩)).eval.1 * p2d_ketPredProj S := by
        apply matrix_ext_ket; intro β
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, p2d_ketPredProj_mul_ket, ket_H]
        have hs0 : S (Function.update β (r ⟨k, hk⟩) 0) ↔ S β :=
          hS _ _ fun w hw ↦ Function.update_of_ne (hw ⟨k, hk⟩) _ _
        have hs1 : S (Function.update β (r ⟨k, hk⟩) 1) ↔ S β :=
          hS _ _ fun w hw ↦ Function.update_of_ne (hw ⟨k, hk⟩) _ _
        by_cases hβ : S β
        · rw [ite_eq_left hβ, ket_H, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
              p2d_ketPredProj_mul_ket, p2d_ketPredProj_mul_ket,
              ite_eq_left (hs0.mpr hβ), ite_eq_left (hs1.mpr hβ)]
        · rw [ite_eq_right hβ, Matrix.mulVec_zero, Matrix.mulVec_smul, Matrix.mulVec_add,
              Matrix.mulVec_smul, p2d_ketPredProj_mul_ket, p2d_ketPredProj_mul_ket,
              ite_eq_right (mt hs0.mp hβ), ite_eq_right (mt hs1.mp hβ), smul_zero, add_zero,
                  smul_zero]
      change p2d_ketPredProj S * ((Circuit.H (r ⟨k, hk⟩)).eval.1 * (cHadRegAux r k (by
          omega)).eval.1) =
        ((Circuit.H (r ⟨k, hk⟩)).eval.1 * (cHadRegAux r k (by omega)).eval.1) * p2d_ketPredProj S
      rw [← mul_assoc, hH, mul_assoc, ih, ← mul_assoc]
theorem cHadReg_preserves_ketPredProj {n K : ℕ} (r : QRegister K n)
    (S : BitAssignment n → Prop) (hS : ∀ β₁ β₂ : BitAssignment n, (∀ w, (∀ t : Fin K, w ≠ r t)
    → β₁ w = β₂ w) → (S β₁ ↔ S β₂)) : p2d_ketPredProj S * (cHadReg r).eval.1 =
    (cHadReg r).eval.1 * p2d_ketPredProj S := cHadRegAux_preserves_ketPredProj r S hS K le_rfl
theorem permUnitary_mulVec_single_one {d : ℕ} (σ : Equiv.Perm (Fin d)) (w : Fin d) :
    (Operator.permutationUnitary σ).1.mulVec (Pi.single w 1) = Pi.single (σ w) 1 := by
  funext i
  rw [Matrix.mulVec_single_one]
  change (Operator.permutationUnitary σ).1 i w = (Pi.single (σ w) (1 : ℂ) : Fin d → ℂ) i
  rw [permUnitary_apply_local]
  by_cases h : σ w = i
  · subst h; simp
  · have hne : i ≠ σ w := Ne.symm h
    simp [h, hne]
theorem embedUnitary_permutationUnitary_mulVec_single {n k : ℕ}
    (r : QRegister k n) (σ : Equiv.Perm (Fin (2 ^ k))) (g : Fin (2 ^ n)) :
    (r.embedUnitary (Operator.permutationUnitary σ)).1.mulVec (Pi.single g 1) =
      Pi.single (r.replaceIndex g (σ (r.extractIndex g))) 1 := by
  rw [QRegister.embedUnitary_val, r.embedMatrix_mulVec_single_factors,
      permUnitary_mulVec_single_one, QRegister.tensorState_single_replaceIndex]
theorem embedUnitary_uLensLoad_mulVec_single {n kData : ℕ} (rData : QRegister kData n)
    (rMeas : QRegister 18 n) (hDM : rData.DisjointWires rMeas) (L : Slot18Lens kData)
    (g : Fin (2 ^ n)) : ((rData.concat rMeas hDM).embedUnitary (uLensLoad L)).1.mulVec
    (Pi.single g 1) = Pi.single (rMeas.replaceIndex g (xor18 (rMeas.extractIndex g) (L.tbl
    (rData.extractIndex g)))) 1 := by
  let rAct := rData.concat rMeas hDM
  let selD := selDataInAct kData
  let selM := selMeasInAct kData
  have hD : rAct.compose selD = rData := concat_compose_selDataInAct rData rMeas hDM
  have hM : rAct.compose selM = rMeas := concat_compose_selMeasInAct rData rMeas hDM
  have hDg : selD.extractIndex (rAct.extractIndex g) = rData.extractIndex g :=
    (extractIndex_compose_eq rAct selD g).trans (congrArg (fun r : QRegister kData n ↦
        r.extractIndex g) hD)
  have hMg : selM.extractIndex (rAct.extractIndex g) = rMeas.extractIndex g :=
    (extractIndex_compose_eq rAct selM g).trans (congrArg (fun r : QRegister 18 n ↦ r.extractIndex
        g) hM)
  dsimp only [uLensLoad]
  rw [embedUnitary_permutationUnitary_mulVec_single]
  refine congrArg (fun idx ↦ (Pi.single idx (1 : ℂ) : Fin (2 ^ n) → ℂ)) ?_
  let v := xor18 (rMeas.extractIndex g) (L.tbl (rData.extractIndex g))
  have hApp : lensLoadEquiv L (rAct.extractIndex g) = selM.replaceIndex (rAct.extractIndex g) v :=
      by
    change liftPairIdx (lensLoadPerm L) (rAct.extractIndex g) = _
    dsimp only [liftPairIdx, extractPair, lensLoadPerm]
    rw [QRegister.replaceIndex_extractIndex, hMg, hDg]
  rw [hApp]
  exact (replaceIndex_compose_eq rAct selM g v).trans
    (congrArg (fun r : QRegister 18 n ↦ r.replaceIndex g v) hM)
theorem embedUnitary_uLensWrite_mulVec_single {n kData : ℕ} (rData : QRegister kData n)
    (rMeas : QRegister 18 n) (hDM : rData.DisjointWires rMeas) (L : Slot18Lens kData)
    (g : Fin (2 ^ n)) : ((rData.concat rMeas hDM).embedUnitary (uLensWrite L)).1.mulVec
    (Pi.single g 1) = Pi.single (rData.replaceIndex g (L.updSlot (rData.extractIndex g) (xor18
    (L.tbl (rData.extractIndex g)) (rMeas.extractIndex g)))) 1 := by
  let rAct := rData.concat rMeas hDM
  let selD := selDataInAct kData
  let selM := selMeasInAct kData
  have hD : rAct.compose selD = rData := concat_compose_selDataInAct rData rMeas hDM
  have hM : rAct.compose selM = rMeas := concat_compose_selMeasInAct rData rMeas hDM
  have hDg : selD.extractIndex (rAct.extractIndex g) = rData.extractIndex g :=
    (extractIndex_compose_eq rAct selD g).trans (congrArg (fun r : QRegister kData n ↦
        r.extractIndex g) hD)
  have hMg : selM.extractIndex (rAct.extractIndex g) = rMeas.extractIndex g :=
    (extractIndex_compose_eq rAct selM g).trans (congrArg (fun r : QRegister 18 n ↦ r.extractIndex
        g) hM)
  dsimp only [uLensWrite]
  rw [embedUnitary_permutationUnitary_mulVec_single]
  refine congrArg (fun idx ↦ (Pi.single idx (1 : ℂ) : Fin (2 ^ n) → ℂ)) ?_
  let dNew := L.updSlot (rData.extractIndex g)
    (xor18 (L.tbl (rData.extractIndex g)) (rMeas.extractIndex g))
  have hApp : lensWriteEquiv L (rAct.extractIndex g) = selD.replaceIndex (rAct.extractIndex g) dNew
      := by
    change liftPairIdx (lensWritePerm L) (rAct.extractIndex g) = _
    dsimp only [liftPairIdx, extractPair, lensWritePerm]
    rw [hDg, hMg]
    refine basisBits_inj fun w ↦ ?_
    by_cases hw : w ∈ Set.range selM.wires
    · obtain ⟨j, rfl⟩ := hw
      rw [QRegister.basisBits_replaceIndex_apply,
          QRegister.basisBits_replaceIndex_of_not_mem selD _ _ (selM j)
            (fun ⟨i, hi⟩ ↦ (selDataInAct_disj_selMeasInAct kData).ne i j hi)]
      have hMj : basisBits 18 (rMeas.extractIndex g) j =
          basisBits (kData + 18) (rAct.extractIndex g) (selM j) := by
        rw [← hMg]; exact QRegister.basisBits_extractIndex selM (rAct.extractIndex g) j
      exact hMj
    · rw [QRegister.basisBits_replaceIndex_of_not_mem selM _ _ w hw]
  rw [hApp]
  exact (replaceIndex_compose_eq rAct selD g dNew).trans
    (congrArg (fun r : QRegister kData n ↦ r.replaceIndex g dNew) hD)
/-- Single-bit phase-kick target unitary for bit `j` of `shiftedPartnerSlotFast`. -/
noncomputable def uKick1Bit218 {n : ℕ} (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) : Unitary (2 ^ n) :=
  diagSignUnitary fun g ↦
    let β := basisBits n g
    let s₀ := shiftedPartnerSlotFast (fun w ↦ β (rCore w))
    decide (β (rElecSlot rCore s₀ j) * β (rMeas j) = 1)
theorem uKick1Bit218_mulVec_ket {n : ℕ} (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) (β : BitAssignment n) :
    (uKick1Bit218 j rCore rMeas).1.mulVec (ket β) =
      (let s₀ := shiftedPartnerSlotFast (fun w ↦ β (rCore w))
       (-1 : ℂ) ^ (β (rElecSlot rCore s₀ j) * β (rMeas j)).val) • ket β := by
  dsimp only [uKick1Bit218]
  rw [diagSignUnitary_mulVec_ket]
  have hβ : basisBits n ((basisBitsEquiv n).symm β) = β := (basisBitsEquiv n).apply_symm_apply β
  simp only [hβ, ite_decide_eq_one_zmod2]
/-- Prefix phase-kick unitary on the first `k` bits of `rMeas` from `shiftedPartnerSlotFast`. -/
noncomputable def uKickPrefix218 {n : ℕ} (k : ℕ) (hk : k ≤ 18)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) : Unitary (2 ^ n) :=
  diagSignUnitary fun g ↦
    let β := basisBits n g
    let s₀ := shiftedPartnerSlotFast (fun w ↦ β (rCore w))
    decide ((∑ j : Fin k,
      β (rElecSlot rCore s₀ ⟨j.val, by omega⟩) * β (rMeas ⟨j.val, by omega⟩)) = 1)
theorem cHadReg_meas_conj_uKickPrefix218_eq_uLensLoad {n kData : ℕ}
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rMeas : QRegister 18 n) (hDM : rData.DisjointWires rMeas) :
    (cHadReg rMeas).eval * uKickPrefix218 18 le_rfl (rData.compose selCore) rMeas * (cHadReg
        rMeas).eval =
      (rData.concat rMeas hDM).embedUnitary (uLensLoad (shiftedPartnerLens218 selCore)) := by
  let rCore := rData.compose selCore
  let L := shiftedPartnerLens218 selCore
  have hCM : rCore.DisjointWires rMeas := hDM.compose_left selCore
  let bL : Fin 18 → BitAssignment n → ZMod 2 := fun j α ↦
    α (rElecSlot rCore (shiftedPartnerSlotFast (fun w ↦ α (rCore w))) j)
  have hbL : ∀ (j : Fin 18) (α₁ α₂ : BitAssignment n),
      (∀ w, (∀ t : Fin 18, w ≠ rMeas t) → α₁ w = α₂ w) → bL j α₁ = bL j α₂ := fun j α₁ α₂ h ↦ by
    have hSlot : shiftedPartnerSlotFast (fun w ↦ α₁ (rCore w)) =
        shiftedPartnerSlotFast (fun w ↦ α₂ (rCore w)) :=
      shiftedPartnerSlotFast_congr_outside fun w _ _ ↦ h (rCore w) fun t ↦ hCM.ne w t
    dsimp only [bL]; rw [hSlot]
    exact h _ fun t ↦ by simp only [rElecSlot, QRegister.slice_apply]; exact hCM.ne _ t
  have hKickEq : uKickPrefix218 18 le_rfl (rData.compose selCore) rMeas = diagSignUnitary (fun
      g : Fin (2 ^ n) ↦ decide ((∑ j : Fin 18, bL j (basisBits n g) * basisBits n g (rMeas j))
      = 1)) := congrArg diagSignUnitary (funext fun _ ↦ rfl)
  rw [hKickEq]
  apply Subtype.ext; apply matrix_ext_ket; intro β
  rw [cHadReg_conj_phase_ket rMeas bL hbL β]
  let g := (basisBitsEquiv n).symm β
  have hgβ : basisBits n g = β := (basisBitsEquiv n).apply_symm_apply β
  have hKetG : ket β = Pi.single g 1 := rfl
  have hRhs : ((rData.concat rMeas hDM).embedUnitary (uLensLoad L)).1 *ᵥ ket β =
      Pi.single (rMeas.replaceIndex g (xor18 (rMeas.extractIndex g) (L.tbl (rData.extractIndex
          g)))) 1 := by
    rw [hKetG]; exact embedUnitary_uLensLoad_mulVec_single rData rMeas hDM L g
  rw [hRhs]
  change Pi.single ((basisBitsEquiv n).symm (p2d_writeReg β rMeas (fun j ↦ β (rMeas j) + bL j β)))
      1 = _
  refine congrArg (fun idx ↦ (Pi.single idx (1 : ℂ) : Fin (2 ^ n) → ℂ)) ?_
  apply (basisBitsEquiv n).injective; funext w
  rw [(basisBitsEquiv n).apply_symm_apply]
  change p2d_writeReg β rMeas (fun j ↦ β (rMeas j) + bL j β) w =
    basisBits n (rMeas.replaceIndex g (xor18 (rMeas.extractIndex g) (L.tbl (rData.extractIndex
        g)))) w
  by_cases hw : w ∈ Set.range rMeas.wires
  · obtain ⟨j, rfl⟩ := hw
    rw [p2d_writeReg_apply_reg, QRegister.basisBits_replaceIndex_apply, basisBits_xor18,
        QRegister.basisBits_extractIndex, basisBits_shiftedPartnerLens218_tbl_eq rData selCore g j,
        hgβ]
  · rw [p2d_writeReg_apply_of_not_mem _ _ _ _ hw,
        QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hw, hgβ]
/-- **Electron-Only Hadamard Conjugation Write Identity (`0` `rMeas` Hadamards!)**:
Conjugating `uKickPrefix218 18` by `cHadReg (rElec3924 rCore)` directly equals
`embedUnitary (uLensWrite (shiftedPartnerLens218 selCore))`! -/
theorem cHadReg_elec_conj_uKickPrefix218_eq_uLensWrite {n kData : ℕ}
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rMeas : QRegister 18 n) (hDM : rData.DisjointWires rMeas) :
    (cHadReg (rElec3924 (rData.compose selCore))).eval * uKickPrefix218 18 le_rfl
    (rData.compose selCore) rMeas * (cHadReg (rElec3924 (rData.compose selCore))).eval =
    (rData.concat rMeas hDM).embedUnitary (uLensWrite (shiftedPartnerLens218 selCore)) := by
  let rCore := rData.compose selCore
  let rElec := rElec3924 rCore
  let L := shiftedPartnerLens218 selCore
  have hCM : rCore.DisjointWires rMeas := hDM.compose_left selCore
  let bE : Fin 3924 → BitAssignment n → ZMod 2 := fun i α ↦ if i.val / 18 =
      (shiftedPartnerSlotFast (fun w ↦ α (rCore w))).val then α
      (rMeas ⟨i.val % 18, Nat.mod_lt _ (by decide)⟩) else 0
  have hbE : ∀ (i : Fin 3924) (α₁ α₂ : BitAssignment n),
      (∀ w, (∀ t : Fin 3924, w ≠ rElec t) → α₁ w = α₂ w) → bE i α₁ = bE i α₂ := fun i α₁ α₂ h ↦ by
    have hSlot : shiftedPartnerSlotFast (fun w ↦ α₁ (rCore w)) =
        shiftedPartnerSlotFast (fun w ↦ α₂ (rCore w)) :=
      shiftedPartnerSlotFast_congr_outside fun w hwLo _ ↦ h (rCore w) fun t ht ↦ by
        dsimp only [rElec, rElec3924, QRegister.slice_apply] at ht
        have hv := congrArg Fin.val (rCore.wires.injective ht)
        dsimp at hv; have := t.isLt; omega
    have hM : α₁ (rMeas ⟨i.val % 18, Nat.mod_lt _ (by decide)⟩) =
        α₂ (rMeas ⟨i.val % 18, Nat.mod_lt _ (by decide)⟩) :=
      h _ fun t ht ↦ by
        dsimp only [rElec, rElec3924, QRegister.slice_apply] at ht
        exact (hCM.ne _ _ ht.symm)
    dsimp only [bE]; rw [hSlot, hM]
  have hSumEq : ∀ α : BitAssignment n,
      (∑ i : Fin 3924, bE i α * α (rElec i)) =
        let s₀ := shiftedPartnerSlotFast (fun w ↦ α (rCore w))
        ∑ j : Fin 18, α (rElecSlot rCore s₀ j) * α (rMeas j) := fun α ↦ by
    let s₀ := shiftedPartnerSlotFast (fun w ↦ α (rCore w))
    have hFilt : (∑ i : Fin 3924, bE i α * α (rElec i)) = ∑ i ∈ Finset.univ.filter
        (fun i : Fin 3924 ↦ i.val / 18 = s₀.val), bE i α * α (rElec i) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      by_cases hi : i.val / 18 = s₀.val
      · rw [ite_eq_left hi]
      · rw [ite_eq_right hi]; dsimp only [bE]; rw [ite_eq_right hi, zero_mul]
    rw [hFilt]
    refine (Finset.sum_bij'
      (fun (j : Fin 18) _ ↦ (⟨18 * s₀.val + j.val, by have := s₀.isLt; have := j.isLt; omega⟩ : Fin
          3924))
      (fun (i : Fin 3924) _ ↦ (⟨i.val % 18, Nat.mod_lt _ (by decide)⟩ : Fin 18))
      (fun j _ ↦ Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; have := j.isLt; omega⟩)
      (fun _ _ ↦ Finset.mem_univ _)
      (fun j _ ↦ Fin.ext (by dsimp; have := j.isLt; omega))
      (fun i hi ↦ Fin.ext (by have h := (Finset.mem_filter.mp hi).2; dsimp at h ⊢; omega))
      (fun j _ ↦ ?_)).symm
    dsimp only [bE]
    have hdiv : (18 * s₀.val + j.val) / 18 = s₀.val := by have := j.isLt; omega
    have hmod : (⟨(18 * s₀.val + j.val) % 18, Nat.mod_lt _ (by decide)⟩ : Fin 18) = j :=
      Fin.ext (by dsimp; have := j.isLt; omega)
    rw [ite_eq_left hdiv, hmod, ← rElecSlot_eq_rElec3924 rCore s₀ j, mul_comm]
  have hKickEq : uKickPrefix218 18 le_rfl (rData.compose selCore) rMeas =
      diagSignUnitary (fun g : Fin (2 ^ n) ↦
        decide ((∑ i : Fin 3924, bE i (basisBits n g) * basisBits n g (rElec i)) = 1)) := by
    refine congrArg diagSignUnitary (funext fun g ↦ ?_)
    dsimp only
    rw [hSumEq (basisBits n g)]
  rw [hKickEq]
  apply Subtype.ext; apply matrix_ext_ket; intro β
  rw [cHadReg_conj_phase_ket (rElec3924 (rData.compose selCore)) bE hbE β]
  let g := (basisBitsEquiv n).symm β
  have hgβ : basisBits n g = β := (basisBitsEquiv n).apply_symm_apply β
  have hKetG : ket β = Pi.single g 1 := rfl
  have hRhs : ((rData.concat rMeas hDM).embedUnitary (uLensWrite L)).1 *ᵥ ket β = Pi.single
      (rData.replaceIndex g (L.updSlot (rData.extractIndex g) (xor18 (L.tbl
      (rData.extractIndex g)) (rMeas.extractIndex g)))) 1 := by
    rw [hKetG]; exact embedUnitary_uLensWrite_mulVec_single rData rMeas hDM L g
  rw [hRhs]
  change Pi.single ((basisBitsEquiv n).symm (p2d_writeReg β rElec (fun i ↦ β (rElec i) + bE i β)))
      1 = _
  refine congrArg (fun idx ↦ (Pi.single idx (1 : ℂ) : Fin (2 ^ n) → ℂ)) ?_
  let d := rData.extractIndex g
  let v := xor18 (L.tbl d) (rMeas.extractIndex g)
  let s₀ := shiftedPartnerSlotFast (fun w ↦ β (rCore w))
  have hSlotG : shiftedPartnerSlotFast (fun w ↦ basisBits kData d (selCore w)) = s₀ := by
    refine shiftedPartnerSlotFast_congr_outside fun w _ _ ↦ ?_
    rw [QRegister.basisBits_extractIndex rData g (selCore w), hgβ]
    rfl
  have hCompSlot : rData.compose (shiftedPartnerSlotReg selCore d) = rElecSlot rCore s₀ := by
    ext j
    exact congrArg Fin.val (by
      dsimp only [shiftedPartnerSlotReg, QRegister.compose_apply]
      rw [hSlotG]
      rfl)
  have hRepSlot : rData.replaceIndex g (L.updSlot d v) = (rElecSlot rCore s₀).replaceIndex g v := by
    dsimp only [L, shiftedPartnerLens218]
    exact (replaceIndex_compose_eq rData (shiftedPartnerSlotReg selCore d) g v).trans
      (congrArg (fun r : QRegister 18 n ↦ r.replaceIndex g v) hCompSlot)
  rw [hRepSlot]
  apply (basisBitsEquiv n).injective; funext w
  rw [(basisBitsEquiv n).apply_symm_apply]
  change p2d_writeReg β rElec (fun i ↦ β (rElec i) + bE i β) w =
    basisBits n ((rElecSlot rCore s₀).replaceIndex g v) w
  by_cases hwS : w ∈ Set.range (rElecSlot rCore s₀).wires
  · obtain ⟨j, rfl⟩ := hwS
    rw [QRegister.basisBits_replaceIndex_apply, basisBits_xor18,
        basisBits_shiftedPartnerLens218_tbl_eq rData selCore g j,
        QRegister.basisBits_extractIndex rMeas g j]
    have hSlotG2 : shiftedPartnerSlotFast (fun w ↦ basisBits n g (rCore w)) = s₀ := by
      dsimp only [s₀]; rw [hgβ]
    rw [hSlotG2, hgβ]
    let i₀ : Fin 3924 := ⟨18 * s₀.val + j.val, by have := s₀.isLt; have := j.isLt; omega⟩
    have hwE : rElecSlot rCore s₀ j = rElec i₀ := rElecSlot_eq_rElec3924 rCore s₀ j
    rw [hwE, p2d_writeReg_apply_reg]
    dsimp only [bE, i₀]
    have hdiv : (18 * s₀.val + j.val) / 18 = s₀.val := by have := j.isLt; omega
    have hmod : (⟨(18 * s₀.val + j.val) % 18, Nat.mod_lt _ (by decide)⟩ : Fin 18) = j :=
      Fin.ext (by dsimp; have := j.isLt; omega)
    rw [ite_eq_left hdiv, hmod]
  · rw [QRegister.basisBits_replaceIndex_of_not_mem _ _ _ _ hwS, hgβ]
    by_cases hwE : w ∈ Set.range rElec.wires
    · obtain ⟨i, rfl⟩ := hwE
      rw [p2d_writeReg_apply_reg]
      have hne : i.val / 18 ≠ s₀.val := fun hdiv ↦ hwS ⟨⟨i.val % 18, Nat.mod_lt _ (by decide)⟩, by
        rw [rElecSlot_eq_rElec3924 rCore s₀]
        exact congrArg rElec.wires (Fin.ext (by dsimp; omega))⟩
      dsimp only [bE]
      rw [ite_eq_right hne, add_zero]
    · exact p2d_writeReg_apply_of_not_mem _ _ _ _ hwE
private theorem eval_H_embedUnitary {n kAct : ℕ} (rAct : QRegister kAct n) (q : Wire kAct) :
    (Circuit.H (rAct q)).eval = rAct.embedUnitary (Circuit.H q).eval := by
  apply Subtype.ext
  have hComp : rAct.compose (QRegister.singleton q) = QRegister.singleton (rAct q) := by
    ext idx; fin_cases idx; rfl
  exact (congrArg (fun r : QRegister 1 n ↦ r.embedMatrix (PrimitiveGate.eval PrimitiveGate.H).1)
      hComp.symm).trans
    (rAct.embedMatrix_compose (QRegister.singleton q) (PrimitiveGate.eval PrimitiveGate.H).1)
theorem cHadRegAux_comm_of_wire_comm {n K : ℕ} (r : QRegister K n) (U : Unitary (2 ^ n))
    (h : ∀ i : Fin K, (Circuit.H (r i)).eval * U = U * (Circuit.H (r i)).eval) :
    ∀ (k : ℕ) (hk : k ≤ K),
      (cHadRegAux r k hk).eval * U = U * (cHadRegAux r k hk).eval
  | 0, _ => by
      change 1 * U = U * 1
      rw [one_mul, mul_one]
  | k + 1, hk => by
      have ih := cHadRegAux_comm_of_wire_comm r U h k (by omega)
      change ((Circuit.H (r ⟨k, hk⟩)).eval * (cHadRegAux r k (by omega)).eval) * U =
        U * ((Circuit.H (r ⟨k, hk⟩)).eval * (cHadRegAux r k (by omega)).eval)
      rw [mul_assoc, ih, ← mul_assoc, h ⟨k, hk⟩, mul_assoc]
theorem cHadReg_comm_of_wire_comm {n K : ℕ} (r : QRegister K n) (U : Unitary (2 ^ n)) (h : ∀ i
    : Fin K, (Circuit.H (r i)).eval * U = U * (Circuit.H (r i)).eval) : (cHadReg r).eval * U =
    U * (cHadReg r).eval := cHadRegAux_comm_of_wire_comm r U h K le_rfl
theorem cHadReg_elec_comm_of_elec3924Preserved {n kData : ℕ} (rData : QRegister kData n)
    (selCore : QRegister posCoreWires kData) (rMeas : QRegister 18 n)
    (hDM : rData.DisjointWires rMeas) {uMid : Unitary (2 ^ (kData + 18))}
    (hElec : Elec3924Preserved selCore uMid) :
    (cHadReg (rElec3924 (rData.compose selCore))).eval * (rData.concat rMeas hDM).embedUnitary
    uMid = (rData.concat rMeas hDM).embedUnitary uMid *
    (cHadReg (rElec3924 (rData.compose selCore))).eval := by
  let rAct := rData.concat rMeas hDM
  have hD : rAct.compose (selDataInAct kData) = rData := concat_compose_selDataInAct rData rMeas hDM
  refine cHadReg_comm_of_wire_comm (rElec3924 (rData.compose selCore)) (rAct.embedUnitary uMid) fun
      i ↦ ?_
  have hWire : rElec3924 (rData.compose selCore) i = rAct (rElecInAct selCore i) := by
    dsimp only [rElecInAct, QRegister.compose_apply]
    exact (congrArg (fun r : QRegister kData n ↦ r (rElec3924 selCore i)) hD).symm
  rw [hWire, eval_H_embedUnitary rAct (rElecInAct selCore i),
      ← rAct.embedUnitary_mul, hElec.1 i, rAct.embedUnitary_mul]
-- ============================================================================
-- Section 3B: Parametric 4-Row Primitives (`cLoad4Rows218Into`, `dSelectKickFrom4Rows`,
--             `dUncompute4Rows218`), `uHold1Bit`, `dLoadHole218`, & `dFixHole218`
-- ============================================================================
theorem neg_one_pow_zmod2_add (a b : ZMod 2) :
    (-1 : ℂ) ^ (a + b).val = (-1 : ℂ) ^ a.val * (-1 : ℂ) ^ b.val := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl
  · simp
  · simp
  · simp
  · change (-1 : ℂ) ^ (0 : ZMod 2).val = (-1 : ℂ) ^ 1 * (-1 : ℂ) ^ 1
    norm_num
theorem neg_one_pow_sum_zmod2 {k : ℕ} (g : Fin k → ZMod 2) :
    (-1 : ℂ) ^ (∑ i : Fin k, g i).val = ∏ i : Fin k, (-1 : ℂ) ^ (g i).val := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Fin.sum_univ_castSucc, Fin.prod_univ_castSucc, neg_one_pow_zmod2_add, ih]
theorem embedUnitary_diagSignUnitary {n kAct : ℕ}
    (rAct : QRegister kAct n) (p : Fin (2 ^ kAct) → Bool) :
    rAct.embedUnitary (diagSignUnitary p) = diagSignUnitary (fun g ↦ p (rAct.extractIndex g)) := by
  ext i j
  rw [QRegister.embedUnitary_val, QRegister.embedMatrix_apply]
  by_cases hij : i = j
  · subst hij; simp [diagSignUnitary]
  · split_ifs with henv
    · have hexNe : rAct.extractIndex i ≠ rAct.extractIndex j := fun hex ↦ hij <| by
        apply (basisBitsEquiv n).injective; funext w
        by_cases hw : w ∈ Set.range rAct.wires
        · obtain ⟨k, rfl⟩ := hw
          change basisBits n i (rAct k) = basisBits n j (rAct k)
          rw [← QRegister.basisBits_extractIndex, ← QRegister.basisBits_extractIndex, hex]
        · exact ((rAct.basisSplit_environment_eq_iff i j).mp henv) w hw
      simp [diagSignUnitary, hexNe, hij]
    · simp [diagSignUnitary, hij]
theorem subspaceStep_measureXReset {Var : Type} [Fintype Var] [DecidableEq Var] {n k : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rOut : QRegister k n) {R₁ R₂ : Operator (2 ^ n)}
    {cont : (Fin k → Bool) → DynamicCircuit Var n} (hCont : ∀ f : Fin k → Bool, SubspaceStep
    (DynCircuitExt.xResetKraus rOut f * R₁) ((((√(1 / 2)) ^ k : ℝ) : ℂ) • R₂) (cont f)) :
    SubspaceStep R₁ R₂ (DynCircuitExt.measureXResetAndBranch v k rOut cont) := by
  intro M
  choose MCont hCont_wp hCont_eq using fun f ↦ hCont f M
  obtain ⟨MMid, hMid_wp, hMid_mat⟩ :=
    DynCircuitExt.wp_measureXResetAndBranch_const v k rOut cont M MCont hCont_wp
  refine ⟨MMid, hMid_wp, ?_⟩
  rw [hMid_mat, Matrix.mul_sum, Matrix.sum_mul]
  let w : ℝ := (√(1 / 2)) ^ k
  have hstar : star (w : ℂ) = (w : ℂ) := Complex.conj_ofReal w
  have hTerm : ∀ f : Fin k → Bool,
      R₁ᴴ * ((DynCircuitExt.xResetKraus rOut f)ᴴ * (MCont f).1.1 *
        DynCircuitExt.xResetKraus rOut f) * R₁ =
      ((w ^ 2 : ℝ) : ℂ) • (R₂ᴴ * M.1.1 * R₂) := fun f ↦ by
    calc R₁ᴴ * ((DynCircuitExt.xResetKraus rOut f)ᴴ * (MCont f).1.1 *
          DynCircuitExt.xResetKraus rOut f) * R₁
        = (DynCircuitExt.xResetKraus rOut f * R₁)ᴴ * (MCont f).1.1 *
            (DynCircuitExt.xResetKraus rOut f * R₁) := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = ((w : ℂ) • R₂)ᴴ * M.1.1 * ((w : ℂ) • R₂) := (hCont_eq f).symm
      _ = ((w ^ 2 : ℝ) : ℂ) • (R₂ᴴ * M.1.1 * R₂) := by
            simp only [Matrix.conjTranspose_smul, hstar, Matrix.smul_mul,
              Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
            congr 1; push_cast; ring
  rw [Finset.sum_congr rfl fun f _ ↦ hTerm f, ← Finset.sum_smul]
  have hsum_c : (∑ _f : Fin k → Bool, ((w ^ 2 : ℝ) : ℂ)) = 1 := by
    exact_mod_cast DynCircuitExt.sum_sqrt_half_pow_sq k
  rw [hsum_c, one_smul]
/-- Wire-disjointness bundle for a 4-wire row buffer `rRow4` (satisfied both by
`p2dSubReg rScr 70 4 _` and by any held 4-wire chunk disjoint from `rCore` and `rScr`). -/
abbrev RowBufDisj {n mScr : ℕ} (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (rRow4 : QRegister 4 n) : Prop := rCore.DisjointWires rRow4 ∧ (∀ (k : Fin mScr) (r : Fin
    4), (k.val < 70 ∨ 74 ≤ k.val) → rScr k ≠ rRow4 r)
theorem rowBufDisj_scr70 {n mScr : ℕ} (hm : 75 ≤ mScr) (rCore : QRegister posCoreWires n)
    (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rScr) : RowBufDisj rCore rScr
    (p2dSubReg rScr 70 4 (by omega)) := by
  refine ⟨?_, fun k r hk heq ↦ ?_⟩
  · rw [QRegister.disjoint_iff]; intro i r h
    have hr : p2dSubReg rScr 70 4 (by omega) r = rScr ⟨70 + r.val, by omega⟩ :=
      congrArg rScr.wires (Fin.ext (by dsimp [p2dSubReg]))
    exact hCS.ne i ⟨70 + r.val, by omega⟩ (h.trans hr)
  · have hr : p2dSubReg rScr 70 4 (by omega) r = rScr ⟨70 + r.val, by omega⟩ :=
      congrArg rScr.wires (Fin.ext (by dsimp [p2dSubReg]))
    have hv := congrArg Fin.val (rScr.wires.injective (heq.trans hr))
    dsimp at hv; have := r.isLt; omega
/-- Row-loaded bit value for row `r : Fin 4` of the `64 × 4` `218`-slot table (`0 .. 217`, `KRem =
  26`). -/
def rowBit218 {n : ℕ} (rCore : QRegister posCoreWires n) (j : Fin 18)
    (β : BitAssignment n) (l₀ : ℕ) (r : Fin 4) : ZMod 2 :=
  if hr3 : r.val < 3 then
    if hl : l₀ < 64 then β (rElecSlot rCore ⟨64 * r.val + l₀, by omega⟩ j) else 0
  else if hlt26 : l₀ < 26 then
    β (rElecSlot rCore ⟨192 + l₀, by omega⟩ j)
  else
    β (rElecSlot rCore ⟨192, by decide⟩ j)
theorem rowBit218_at_active {n : ℕ} (rCore : QRegister posCoreWires n) (j : Fin 18)
    (β : BitAssignment n) (s₀ : Fin 218) :
    rowBit218 rCore j β (s₀.val % 64) ⟨s₀.val / 64, by have := s₀.isLt; omega⟩ =
      β (rElecSlot rCore s₀ j) := by
  have hs := s₀.isLt
  let l₀ := s₀.val % 64
  let h₀ := s₀.val / 64
  have hl₀ : l₀ < 64 := Nat.mod_lt _ (by decide)
  have hdiv : 64 * h₀ + l₀ = s₀.val := Nat.div_add_mod s₀.val 64
  dsimp only [rowBit218]
  by_cases hh3 : h₀ < 3
  · rw [dite_eq_left hh3, dite_eq_left hl₀]
    exact congrArg (fun e ↦ β (rElecSlot rCore e j)) (Fin.ext (by dsimp; omega))
  · have hh_eq : h₀ = 3 := by omega
    have hlt26 : l₀ < 26 := by omega
    rw [dite_eq_right hh3, dite_eq_left hlt26]
    exact congrArg (fun e ↦ β (rElecSlot rCore e j)) (Fin.ext (by dsimp; omega))
theorem rowBit218_congr_elec {n : ℕ} (rCore : QRegister posCoreWires n) (j : Fin 18)
    {β₁ β₂ : BitAssignment n} (hE : ∀ e : Fin 218, β₁ (rElecSlot rCore e j) = β₂ (rElecSlot
    rCore e j)) (l₀ : ℕ) (r : Fin 4) : rowBit218 rCore j β₁ l₀ r = rowBit218 rCore j β₂ l₀ r
    := by
  dsimp only [rowBit218]
  split_ifs <;> first | rfl | exact hE _
/-- Z-basis XOR map toggling `rowBit218 rCore j` into `rRow4 : QRegister 4 n`. -/
noncomputable def hold1BitMap {n : ℕ} (rCore : QRegister posCoreWires n) (rRow4 : QRegister 4 n)
    (j : Fin 18) (β : BitAssignment n) : BitAssignment n :=
  let s₀ := shiftedPartnerSlotFast (fun w ↦ β (rCore w))
  p2d_writeReg β rRow4 fun r ↦
    β (rRow4 r) + rowBit218 rCore j β (s₀.val % 64) r
theorem hold1BitMap_involutive {n : ℕ} (rCore : QRegister posCoreWires n) (rRow4 : QRegister 4 n)
    (j : Fin 18) (hCR : rCore.DisjointWires rRow4) :
    Function.Involutive (hold1BitMap rCore rRow4 j) := fun β ↦ by
  let α := hold1BitMap rCore rRow4 j β
  have hCoreEq : ∀ w : Wire posCoreWires, α (rCore w) = β (rCore w) :=
    fun w ↦ p2d_writeReg_apply_of_not_mem _ _ _ _ fun ⟨r, hr⟩ ↦ hCR.ne w r hr.symm
  have hSlot : shiftedPartnerSlotFast (fun w ↦ α (rCore w)) = shiftedPartnerSlotFast
      (fun w ↦ β (rCore w)) := congrArg shiftedPartnerSlotFast (funext hCoreEq)
  have hpw : posCoreWires = 4034 := rfl
  have hRowEq : ∀ (l₀ : ℕ) (r : Fin 4), rowBit218 rCore j α l₀ r = rowBit218 rCore j β l₀ r :=
    fun l₀ r ↦ rowBit218_congr_elec rCore j
      (fun e ↦ p2d_writeReg_apply_of_not_mem _ _ _ _ fun ⟨r', hr'⟩ ↦
        hCR.ne ⟨18 * e.val + j.val, by have := e.isLt; have := j.isLt; omega⟩ r' hr'.symm) l₀ r
  funext w
  change p2d_writeReg α rRow4 (fun r ↦ α (rRow4 r) +
      rowBit218 rCore j α ((shiftedPartnerSlotFast (fun w ↦ α (rCore w))).val % 64) r) w = β w
  rw [hSlot]
  by_cases hw : w ∈ Set.range rRow4.wires
  · obtain ⟨r, rfl⟩ := hw
    rw [p2d_writeReg_apply_reg, hRowEq]
    dsimp only [α, hold1BitMap]
    rw [p2d_writeReg_apply_reg, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · exact (p2d_writeReg_apply_of_not_mem _ _ _ _ hw).trans
      (p2d_writeReg_apply_of_not_mem _ _ _ _ hw)
noncomputable def hold1BitEquiv {n : ℕ} (rCore : QRegister posCoreWires n) (rRow4 : QRegister 4 n)
    (j : Fin 18) (hCR : rCore.DisjointWires rRow4) : Equiv.Perm (Fin (2 ^ n)) :=
  let F : Fin (2 ^ n) → Fin (2 ^ n) := fun g ↦
    (basisBitsEquiv n).symm (hold1BitMap rCore rRow4 j (basisBits n g))
  have hInv : Function.Involutive F := fun g ↦ by
    dsimp only [F]
    have h1 : basisBits n ((basisBitsEquiv n).symm (hold1BitMap rCore rRow4 j (basisBits n g))) =
        hold1BitMap rCore rRow4 j (basisBits n g) := (basisBitsEquiv n).apply_symm_apply _
    rw [h1, hold1BitMap_involutive rCore rRow4 j hCR]
    exact (basisBitsEquiv n).symm_apply_apply g
  Equiv.ofBijective F hInv.bijective
/-- Involutive Z-basis unitary `uHold1Bit` XORing `rowBit218 rCore j` into `rRow4`. -/
noncomputable def uHold1Bit {n : ℕ} (rCore : QRegister posCoreWires n) (rRow4 : QRegister 4 n)
    (j : Fin 18) (hCR : rCore.DisjointWires rRow4) : Unitary (2 ^ n) :=
  Operator.permutationUnitary (hold1BitEquiv rCore rRow4 j hCR)
theorem uHold1Bit_mulVec_ket {n : ℕ} (rCore : QRegister posCoreWires n) (rRow4 : QRegister 4 n)
    (j : Fin 18) (hCR : rCore.DisjointWires rRow4) (β : BitAssignment n) :
    (uHold1Bit rCore rRow4 j hCR).1 *ᵥ ket β = ket (hold1BitMap rCore rRow4 j β) := by
  let g := (basisBitsEquiv n).symm β
  have hg : basisBits n g = β := (basisBitsEquiv n).apply_symm_apply β
  have hKet : ket β = Pi.single g 1 := rfl
  rw [hKet]
  dsimp only [uHold1Bit]
  change (Operator.permutationUnitary (hold1BitEquiv rCore rRow4 j hCR)).1.mulVec (Pi.single g 1) =
      _
  rw [permUnitary_mulVec_single_one]
  dsimp only [hold1BitEquiv]
  rw [Equiv.ofBijective_apply, hg]
  rfl
theorem ketPredProj_mul_of_supportedOn {n : ℕ} {Pred : BitAssignment n → Prop}
    {R : Operator (2 ^ n)} (hSupp : SupportedOn Pred R) : p2d_ketPredProj Pred * R = R := by
  classical
  have h := hSupp (p2d_ketPredProj Pred) 1 fun β hP ↦ by
    rw [p2d_ketPredProj_mul_ket, ite_eq_left hP, Matrix.one_mulVec]
  rwa [Matrix.one_mul] at h
theorem supportedOn_mono {n : ℕ} {P Q : BitAssignment n → Prop} (hPQ : ∀ β, P β → Q β)
    {R : Operator (2 ^ n)} (hSupp : SupportedOn P R) : SupportedOn Q R := fun A B hAB ↦ hSupp
    A B fun β hP ↦ hAB β (hPQ β hP)
theorem supportedOn_and {n : ℕ} {P Q : BitAssignment n → Prop} {R : Operator (2 ^ n)}
    (hP : SupportedOn P R) (hQ : SupportedOn Q R) : SupportedOn (fun β ↦ P β ∧ Q β) R := by
  intro A B hAB
  have h1 := ketPredProj_mul_of_supportedOn hP
  have h2 := ketPredProj_mul_of_supportedOn hQ
  have h12 : p2d_ketPredProj (fun β ↦ P β ∧ Q β) * R = R := by
    rw [← p2d_ketPredProj_mul_ketPredProj_local, Matrix.mul_assoc, h2, h1]
  rw [← h12, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  exact congrArg (· * R) (supportedOn_ketPredProj _ _ (fun _ h ↦ h) A B hAB)
theorem supportedOn_diagSignUnitary_mul {n : ℕ} {Pred : BitAssignment n → Prop}
    (p : Fin (2 ^ n) → Bool) {R : Operator (2 ^ n)} (hSupp : SupportedOn Pred R) :
    SupportedOn Pred ((diagSignUnitary p).1 * R) := fun A B hAB ↦ by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  exact hSupp (A * (diagSignUnitary p).1) (B * (diagSignUnitary p).1) fun β hP ↦ by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, diagSignUnitary_mulVec_ket,
        Matrix.mulVec_smul, Matrix.mulVec_smul, hAB β hP]
theorem supportedOn_cHadReg_mul {n K : ℕ} (r : QRegister K n) {P : BitAssignment n → Prop} (hP
    : ∀ β₁ β₂ : BitAssignment n, (∀ w, (∀ i : Fin K, w ≠ r i) → β₁ w = β₂ w) → (P β₁ ↔ P β₂))
    {R : Operator (2 ^ n)} (hSupp : SupportedOn P R) : SupportedOn P ((cHadReg r).eval.1 * R)
    := by
  have hPR : p2d_ketPredProj P * R = R := ketPredProj_mul_of_supportedOn hSupp
  have hComm := cHadReg_preserves_ketPredProj r P hP
  have hEq : p2d_ketPredProj P * ((cHadReg r).eval.1 * R) = (cHadReg r).eval.1 * R := by
    rw [← Matrix.mul_assoc, hComm, Matrix.mul_assoc, hPR]
  rw [← hEq]
  exact supportedOn_mul_right (supportedOn_ketPredProj P P fun _ h ↦ h) _
/-- Base `.hole` invariant on `rScr` excluding `rScr[70 .. 74)` (`uLo`, `uHi`, `wPar = 0`, `wSel =
  0`). -/
def InvHoleBase218 {n mScr : ℕ} (hm : 75 ≤ mScr) (rCore : QRegister posCoreWires n)
    (rScr : QRegister mScr n) (β : BitAssignment n) : Prop :=
  let s₀ := shiftedPartnerSlotFast (fun w ↦ β (rCore w))
  (∀ l : Fin 64, β (rScr ⟨l.val, by omega⟩) = if l.val = s₀.val % 64 then 1 else 0) ∧
  (∀ h : Fin 4, β (rScr ⟨64 + h.val, by omega⟩) = if h.val = s₀.val / 64 then 1 else 0) ∧
  β (rScr ⟨69, by omega⟩) = 0 ∧
  β (rScr ⟨74, by omega⟩) = 0
theorem invHoleShifted218_iff_base {n mScr : ℕ} (hm : 75 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n) (β : BitAssignment n) :
    InvHoleShifted218 hm rCore rScr β ↔ ((∀ r : Fin 4, β (p2dSubReg rScr 70 4 (by omega) r) =
    0) ∧ InvHoleBase218 hm rCore rScr β) := by
  dsimp only [InvHoleShifted218, InvHoleBase218]
  tauto
theorem hold1BitMap_preserves_invHoleBase218 {n mScr : ℕ} (hm : 75 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n) (rRow4 : QRegister 4 n)
    (j : Fin 18) (hBuf : RowBufDisj rCore rScr rRow4)
    {β : BitAssignment n} (hInv : InvHoleBase218 hm rCore rScr β) :
    InvHoleBase218 hm rCore rScr (hold1BitMap rCore rRow4 j β) := by
  let α := hold1BitMap rCore rRow4 j β
  have hCore : (fun w ↦ α (rCore w)) = fun w ↦ β (rCore w) :=
    funext fun w ↦ p2d_writeReg_apply_of_not_mem _ _ _ _ fun ⟨r, hr⟩ ↦ hBuf.1.ne w r hr.symm
  have hScrOut : ∀ (k : Fin mScr), (k.val < 70 ∨ 74 ≤ k.val) → α (rScr k) = β (rScr k) :=
    fun k hk ↦ p2d_writeReg_apply_of_not_mem _ _ _ _ fun ⟨r, hr⟩ ↦ (hBuf.2 k r hk) hr.symm
  dsimp only [InvHoleBase218] at hInv ⊢
  rw [hCore]
  exact ⟨fun l ↦ (hScrOut ⟨l.val, by omega⟩ (Or.inl (by dsimp; omega))).trans (hInv.1 l),
    fun h ↦ (hScrOut ⟨64 + h.val, by omega⟩ (Or.inl (by dsimp; omega))).trans (hInv.2.1 h),
    (hScrOut ⟨69, by omega⟩ (Or.inl (by dsimp; omega))).trans hInv.2.2.1,
    (hScrOut ⟨74, by omega⟩ (Or.inr (by dsimp; omega))).trans hInv.2.2.2⟩
/-- Loads the 4 `218`-slot row bits for bit `j : Fin 18` into an arbitrary 4-wire buffer `rRow4`
satisfying `RowBufDisj rCore rScr rRow4` (`128 * 3 + 52 = 436 T`, `TOFF = 0`). -/
def cLoad4Rows218Into {n mScr : ℕ} (hm : 75 ≤ mScr) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n) (rRow4 : QRegister 4 n)
    (_hCS : rCore.DisjointWires rScr) (hBuf : RowBufDisj rCore rScr rRow4) : Circuit n :=
  let uLo : Fin 64 → Wire n := fun l ↦ rScr ⟨l.val, by omega⟩
  let wPar : Wire n := rScr ⟨69, by omega⟩
  let c0 := cLoadRowAnchored1Bit 64 64 (by decide) le_rfl uLo (uLo 0)
    (rElecSlot rCore ⟨0, by decide⟩ j)
    (fun i ↦ rElecSlot rCore ⟨1 + i.val, by omega⟩ j)
    (rRow4 ⟨0, by decide⟩)
    (fun _ ↦ rElecSlot_ne_of_slot_ne rCore j _ _ (by omega))
    (fun _ ↦ by simp only [rElecSlot, QRegister.slice_apply]; exact hBuf.1.ne _ _)
    (by simp only [rElecSlot, QRegister.slice_apply]; exact hBuf.1.ne _ _)
    (fun l ↦ hBuf.2 ⟨l.val, by omega⟩ _ (Or.inl (by dsimp; omega)))
    (hBuf.2 ⟨0, by omega⟩ _ (Or.inl (by dsimp; omega)))
  let c1 := cLoadRowAnchored1Bit 64 64 (by decide) le_rfl uLo (uLo 0)
    (rElecSlot rCore ⟨64, by decide⟩ j)
    (fun i ↦ rElecSlot rCore ⟨65 + i.val, by omega⟩ j)
    (rRow4 ⟨1, by decide⟩)
    (fun _ ↦ rElecSlot_ne_of_slot_ne rCore j _ _ (by omega))
    (fun _ ↦ by simp only [rElecSlot, QRegister.slice_apply]; exact hBuf.1.ne _ _)
    (by simp only [rElecSlot, QRegister.slice_apply]; exact hBuf.1.ne _ _)
    (fun l ↦ hBuf.2 ⟨l.val, by omega⟩ _ (Or.inl (by dsimp; omega)))
    (hBuf.2 ⟨0, by omega⟩ _ (Or.inl (by dsimp; omega)))
  let c2 := cLoadRowAnchored1Bit 64 64 (by decide) le_rfl uLo (uLo 0)
    (rElecSlot rCore ⟨128, by decide⟩ j)
    (fun i ↦ rElecSlot rCore ⟨129 + i.val, by omega⟩ j)
    (rRow4 ⟨2, by decide⟩)
    (fun _ ↦ rElecSlot_ne_of_slot_ne rCore j _ _ (by omega))
    (fun _ ↦ by simp only [rElecSlot, QRegister.slice_apply]; exact hBuf.1.ne _ _)
    (by simp only [rElecSlot, QRegister.slice_apply]; exact hBuf.1.ne _ _)
    (fun l ↦ hBuf.2 ⟨l.val, by omega⟩ _ (Or.inl (by dsimp; omega)))
    (hBuf.2 ⟨0, by omega⟩ _ (Or.inl (by dsimp; omega)))
  let cPar := cXorTailParity 64 26 (by decide) (by decide) uLo wPar
    (fun _ ↦ rSub_ne_of_ne rScr (by omega) (by omega) (by omega))
  let c3 := cLoadRowAnchored1Bit 64 26 (by decide) (by decide) uLo wPar
    (rElecSlot rCore ⟨192, by decide⟩ j)
    (fun i ↦ rElecSlot rCore ⟨193 + i.val, by omega⟩ j)
    (rRow4 ⟨3, by decide⟩)
    (fun _ ↦ rElecSlot_ne_of_slot_ne rCore j _ _ (by omega))
    (fun _ ↦ by simp only [rElecSlot, QRegister.slice_apply]; exact hBuf.1.ne _ _)
    (by simp only [rElecSlot, QRegister.slice_apply]; exact hBuf.1.ne _ _)
    (fun l ↦ hBuf.2 ⟨l.val, by omega⟩ _ (Or.inl (by dsimp; omega)))
    (hBuf.2 ⟨69, by omega⟩ _ (Or.inl (by dsimp; omega)))
  c0 ;;ᶜ (c1 ;;ᶜ (c2 ;;ᶜ (cPar ;;ᶜ (c3 ;;ᶜ cPar))))
theorem cLoad4Rows218Into_count_toff {n mScr : ℕ} (hm : 75 ≤ mScr) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n) (rRow4 : QRegister 4 n)
    (hCS : rCore.DisjointWires rScr) (hBuf : RowBufDisj rCore rScr rRow4) :
    (cLoad4Rows218Into hm j rCore rScr rRow4 hCS hBuf).count TOFF = 0 := by
  dsimp only [cLoad4Rows218Into]
  simp only [Circuit.count_seq, cLoadRowAnchored1Bit_count_toff, cXorTailParity_count_toff]
theorem cLoad4Rows218Into_count_t {n mScr : ℕ} (hm : 75 ≤ mScr) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n) (rRow4 : QRegister 4 n)
    (hCS : rCore.DisjointWires rScr) (hBuf : RowBufDisj rCore rScr rRow4) :
    (cLoad4Rows218Into hm j rCore rScr rRow4 hCS hBuf).count T = 436 := by
  dsimp only [cLoad4Rows218Into]
  simp only [Circuit.count_seq, cLoadRowAnchored1Bit_count_t, cXorTailParity_count_t]
theorem cLoad4Rows218Into_eval_ket {n mScr : ℕ} (hm : 75 ≤ mScr) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n) (rRow4 : QRegister 4 n)
    (hCS : rCore.DisjointWires rScr) (hBuf : RowBufDisj rCore rScr rRow4)
    (β : BitAssignment n)
    (hRow0 : ∀ r : Fin 4, β (rRow4 r) = 0)
    (hPar0 : β (rScr ⟨69, by omega⟩) = 0)
    (l₀ : ℕ) (hl₀ : l₀ < 64)
    (hLo : ∀ l : Fin 64, β (rScr ⟨l.val, by omega⟩) = if l.val = l₀ then 1 else 0) :
    (cLoad4Rows218Into hm j rCore rScr rRow4 hCS hBuf).eval.1.mulVec (ket β) =
      ket (p2d_writeReg β rRow4 (rowBit218 rCore j β l₀)) := by
  let uLo : Fin 64 → Wire n := fun l ↦ rScr ⟨l.val, by omega⟩
  let wPar : Wire n := rScr ⟨69, by omega⟩
  let vals := rowBit218 rCore j β l₀
  have hRowNeCore : ∀ (r : Fin 4) (e : Fin 218), rElecSlot rCore e j ≠ rRow4 r :=
    fun r e ↦ by simp only [rElecSlot, QRegister.slice_apply]; exact hBuf.1.ne _ r
  have hRowNeLo : ∀ (r : Fin 4) (l : Fin 64), uLo l ≠ rRow4 r :=
    fun r l ↦ hBuf.2 ⟨l.val, by omega⟩ r (Or.inl (by dsimp; omega))
  have hRowNePar : ∀ (r : Fin 4), wPar ≠ rRow4 r :=
    fun r ↦ hBuf.2 ⟨69, by omega⟩ r (Or.inl (by dsimp; omega))
  have hBnd64 : ∀ α : BitAssignment n,
      (∀ l : Fin 64, α (uLo l) = if l.val = l₀ then 1 else 0) →
      α (uLo 0) = if (l₀ = 0 ∨ 64 ≤ l₀) then 1 else 0 := fun α hα ↦ by
    rw [hα 0]; dsimp
    by_cases h0 : l₀ = 0
    · subst h0; simp
    · rw [ite_eq_right (Ne.symm h0), ite_eq_right (by omega)]
  have hFullRow : ∀ (r : ℕ) (hr : r < 3) (α : BitAssignment n),
      (∀ e : Fin 218, α (rElecSlot rCore e j) = β (rElecSlot rCore e j)) →
      α (rRow4 ⟨r, by omega⟩) = 0 →
      (∀ l : Fin 64, α (uLo l) = if l.val = l₀ then 1 else 0) →
      (cLoadRowAnchored1Bit 64 64 (by decide) le_rfl uLo (uLo 0)
        (rElecSlot rCore ⟨64 * r, by omega⟩ j)
        (fun i ↦ rElecSlot rCore ⟨64 * r + 1 + i.val, by omega⟩ j)
        (rRow4 ⟨r, by omega⟩)
        (fun _ ↦ rElecSlot_ne_of_slot_ne rCore j _ _ (by dsimp; omega))
        (fun _ ↦ hRowNeCore _ _)
        (hRowNeCore _ _)
        (fun l ↦ hRowNeLo _ l)
        (hRowNeLo _ 0)).eval.1.mulVec (ket α) =
      ket (Function.update α (rRow4 ⟨r, by omega⟩) (vals ⟨r, by omega⟩)) := by
    intro r hr α hαCore hαOut hαLo
    rw [cLoadRowAnchored1Bit_eval_ket 64 64 (by decide) le_rfl uLo (uLo 0)
      (rElecSlot rCore ⟨64 * r, by omega⟩ j)
      (fun i ↦ rElecSlot rCore ⟨64 * r + 1 + i.val, by omega⟩ j)
      (rRow4 ⟨r, by omega⟩) _ _ _ _ _
      (fun i₁ i₂ h ↦ Fin.ext (by
        by_contra hne
        exact rElecSlot_ne_of_slot_ne rCore j _ _ (by dsimp; omega) h))
      (fun _ _ ↦ (rCore_ne_rSub hCS _ _ _).symm)
      (fun _ ↦ (rCore_ne_rSub hCS _ _ _).symm)
      α hαOut l₀ hl₀ hαLo (hBnd64 α hαLo)]
    refine congrArg (fun b ↦ ket (Function.update α (rRow4 ⟨r, by omega⟩) b)) ?_
    dsimp only [vals, rowBit218]
    rw [dite_eq_left hr, dite_eq_left hl₀]
    by_cases h0 : l₀ = 0
    · rw [dite_eq_left h0, hαCore]
      exact congrArg (fun e ↦ β (rElecSlot rCore e j)) (Fin.ext (by dsimp; omega))
    · rw [dite_eq_right h0, dite_eq_left hl₀, hαCore]
      exact congrArg (fun e ↦ β (rElecSlot rCore e j)) (Fin.ext (by dsimp; omega))
  let β0 := Function.update β (rRow4 ⟨0, by decide⟩) (vals ⟨0, by decide⟩)
  let β1 := Function.update β0 (rRow4 ⟨1, by decide⟩) (vals ⟨1, by decide⟩)
  let β2 := Function.update β1 (rRow4 ⟨2, by decide⟩) (vals ⟨2, by decide⟩)
  have hStep0 := hFullRow 0 (by decide) β (fun _ ↦ rfl) (hRow0 ⟨0, by decide⟩) hLo
  have hStep1 := hFullRow 1 (by decide) β0
    (fun e ↦ Function.update_of_ne (hRowNeCore _ e) _ _)
    ((Function.update_of_ne (rRow4.wires.injective.ne (Fin.ne_of_val_ne (by dsimp; omega))) _
        _).trans
      (hRow0 ⟨1, by decide⟩))
    (fun l ↦ (Function.update_of_ne (hRowNeLo _ l) _ _).trans (hLo l))
  have hStep2 := hFullRow 2 (by decide) β1
    (fun e ↦ (Function.update_of_ne (hRowNeCore _ e) _ _).trans
      (Function.update_of_ne (hRowNeCore _ e) _ _))
    ((Function.update_of_ne (rRow4.wires.injective.ne (Fin.ne_of_val_ne (by dsimp; omega))) _
        _).trans
      ((Function.update_of_ne (rRow4.wires.injective.ne (Fin.ne_of_val_ne (by dsimp; omega))) _
          _).trans
        (hRow0 ⟨2, by decide⟩)))
    (fun l ↦ (Function.update_of_ne (hRowNeLo _ l) _ _).trans
      ((Function.update_of_ne (hRowNeLo _ l) _ _).trans (hLo l)))
  have hβ2_par : β2 wPar = 0 := by
    dsimp [β2, β1, β0]
    rw [Function.update_of_ne (hRowNePar _), Function.update_of_ne (hRowNePar _),
        Function.update_of_ne (hRowNePar _), hPar0]
  have hβ2_lo : ∀ l : Fin 64, β2 (uLo l) = if l.val = l₀ then 1 else 0 := fun l ↦ by
    dsimp [β2, β1, β0]
    rw [Function.update_of_ne (hRowNeLo _ l), Function.update_of_ne (hRowNeLo _ l),
        Function.update_of_ne (hRowNeLo _ l), hLo l]
  have hβ2_core : ∀ e : Fin 218, β2 (rElecSlot rCore e j) = β (rElecSlot rCore e j) := fun e ↦ by
    dsimp [β2, β1, β0]
    rw [Function.update_of_ne (hRowNeCore _ e), Function.update_of_ne (hRowNeCore _ e),
        Function.update_of_ne (hRowNeCore _ e)]
  have hβ2_r3 : β2 (rRow4 ⟨3, by decide⟩) = 0 := by
    dsimp [β2, β1, β0]
    rw [Function.update_of_ne (rRow4.wires.injective.ne (Fin.ne_of_val_ne (by dsimp; omega))),
        Function.update_of_ne (rRow4.wires.injective.ne (Fin.ne_of_val_ne (by dsimp; omega))),
        Function.update_of_ne (rRow4.wires.injective.ne (Fin.ne_of_val_ne (by dsimp; omega)))]
    exact hRow0 ⟨3, by decide⟩
  let bnd26 : ZMod 2 := if (l₀ = 0 ∨ 26 ≤ l₀) then 1 else 0
  let β3 := Function.update β2 wPar bnd26
  have hPar1 : (cXorTailParity 64 26 (by decide) (by decide) uLo wPar (fun _ ↦ rSub_ne_of_ne
      rScr (by omega) (by omega) (by omega))).eval.1.mulVec (ket β2) = ket β3 := by
    rw [cXorTailParity_eval_ket 64 26 (by decide) (by decide) uLo wPar _ β2 l₀ hl₀ hβ2_lo,
        hβ2_par, zero_add]
  have hβ3_lo : ∀ l : Fin 64, β3 (uLo l) = if l.val = l₀ then 1 else 0 := fun l ↦
    (Function.update_of_ne (rSub_ne_of_ne rScr (by omega) (by omega) (by omega)) _ _).trans (hβ2_lo
        l)
  have hStep3 :
      (cLoadRowAnchored1Bit 64 26 (by decide) (by decide) uLo wPar
        (rElecSlot rCore ⟨192, by decide⟩ j)
        (fun i ↦ rElecSlot rCore ⟨193 + i.val, by omega⟩ j)
        (rRow4 ⟨3, by decide⟩)
        (fun _ ↦ rElecSlot_ne_of_slot_ne rCore j _ _ (by dsimp; omega))
        (fun _ ↦ hRowNeCore _ _)
        (hRowNeCore _ _)
        (fun l ↦ hRowNeLo _ l)
        (hRowNePar _)).eval.1.mulVec (ket β3) =
      ket (Function.update β3 (rRow4 ⟨3, by decide⟩) (vals ⟨3, by decide⟩)) := by
    rw [cLoadRowAnchored1Bit_eval_ket 64 26 (by decide) (by decide) uLo wPar
      (rElecSlot rCore ⟨192, by decide⟩ j)
      (fun i ↦ rElecSlot rCore ⟨193 + i.val, by omega⟩ j)
      (rRow4 ⟨3, by decide⟩) _ _ _ _ _
      (fun i₁ i₂ h ↦ Fin.ext (by
        by_contra hne
        exact rElecSlot_ne_of_slot_ne rCore j _ _ (by dsimp; omega) h))
      (fun _ _ ↦ (rCore_ne_rSub hCS _ _ _).symm)
      (fun _ ↦ (rCore_ne_rSub hCS _ _ _).symm)
      β3
      ((Function.update_of_ne (hRowNePar _).symm _ _).trans hβ2_r3)
      l₀ hl₀ hβ3_lo (Function.update_self _ _ _)]
    refine congrArg (fun b ↦ ket (Function.update β3 (rRow4 ⟨3, by decide⟩) b)) ?_
    have hCore3 : ∀ e : Fin 218, β3 (rElecSlot rCore e j) = β (rElecSlot rCore e j) := fun e ↦
      (Function.update_of_ne (rCore_ne_rSub hCS _ _ _) _ _).trans (hβ2_core e)
    dsimp only [vals, rowBit218]
    rw [dite_eq_right (by decide : ¬ ((3 : ℕ) < 3))]
    by_cases h0 : l₀ = 0
    · rw [dite_eq_left h0, dite_eq_left (by omega : l₀ < 26), hCore3]
      exact congrArg (fun e ↦ β (rElecSlot rCore e j)) (Fin.ext (by dsimp; omega))
    · rw [dite_eq_right h0]
      by_cases hlt26 : l₀ < 26
      · rw [dite_eq_left hlt26, dite_eq_left hlt26, hCore3]
        exact congrArg (fun e ↦ β (rElecSlot rCore e j)) (Fin.ext (by dsimp; omega))
      · rw [dite_eq_right hlt26, dite_eq_right hlt26, hCore3]
  let β4 := Function.update β3 (rRow4 ⟨3, by decide⟩) (vals ⟨3, by decide⟩)
  have hβ4_lo : ∀ l : Fin 64, β4 (uLo l) = if l.val = l₀ then 1 else 0 := fun l ↦
    (Function.update_of_ne (hRowNeLo _ l) _ _).trans (hβ3_lo l)
  have hPar2 : (cXorTailParity 64 26 (by decide) (by decide) uLo wPar
      (fun _ ↦ rSub_ne_of_ne rScr (by omega) (by omega) (by omega))).eval.1.mulVec (ket β4) =
      ket (Function.update β4 wPar (β4 wPar + bnd26)) :=
    cXorTailParity_eval_ket 64 26 (by decide) (by decide) uLo wPar _ β4 l₀ hl₀ hβ4_lo
  dsimp only [cLoad4Rows218Into]
  rw [eval_seq_mulVec, hStep0, eval_seq_mulVec, hStep1, eval_seq_mulVec, hStep2,
      eval_seq_mulVec, hPar1, eval_seq_mulVec, hStep3, hPar2]
  refine congrArg ket ?_
  have hβ4_par : β4 wPar + bnd26 = 0 := by
    dsimp [β4, β3]
    rw [Function.update_of_ne (hRowNePar _), Function.update_self, CharTwo.add_self_eq_zero]
  rw [hβ4_par]
  funext w
  by_cases hwPar : w = wPar
  · subst hwPar
    rw [Function.update_self, p2d_writeReg_apply_of_not_mem _ _ _ _
      (fun ⟨r, hr⟩ ↦ hRowNePar r hr.symm), hPar0]
  · rw [Function.update_of_ne hwPar]
    by_cases hwRow : w ∈ Set.range rRow4.wires
    · obtain ⟨r, rfl⟩ := hwRow
      rw [p2d_writeReg_apply_reg]
      have hr_cases : r = ⟨0, by decide⟩ ∨ r = ⟨1, by decide⟩ ∨ r = ⟨2, by decide⟩ ∨ r = ⟨3, by
          decide⟩ := by
        rcases r with ⟨rv, hrv⟩
        have : rv = 0 ∨ rv = 1 ∨ rv = 2 ∨ rv = 3 := by omega
        rcases this with rfl | rfl | rfl | rfl <;> simp
      rcases hr_cases with rfl | rfl | rfl | rfl
      · dsimp [β4, β3, β2, β1, β0]
        rw [Function.update_of_ne (rRow4.wires.injective.ne (by decide)),
            Function.update_of_ne (hRowNePar _).symm,
            Function.update_of_ne (rRow4.wires.injective.ne (by decide)),
            Function.update_of_ne (rRow4.wires.injective.ne (by decide)),
            Function.update_self]
      · dsimp [β4, β3, β2, β1, β0]
        rw [Function.update_of_ne (rRow4.wires.injective.ne (by decide)),
            Function.update_of_ne (hRowNePar _).symm,
            Function.update_of_ne (rRow4.wires.injective.ne (by decide)),
            Function.update_self]
      · dsimp [β4, β3, β2, β1, β0]
        rw[Function.update_of_ne (rRow4.wires.injective.ne (by decide)),
            Function.update_of_ne (hRowNePar _).symm, Function.update_self]
      · dsimp [β4]; exact Function.update_self _ _ _
    · rw [p2d_writeReg_apply_of_not_mem _ _ _ _ hwRow]
      dsimp [β4, β3, β2, β1, β0]
      rw[Function.update_of_ne (fun h ↦ hwRow ⟨_, h.symm⟩), Function.update_of_ne hwPar,
          Function.update_of_ne (fun h ↦ hwRow ⟨_, h.symm⟩),
          Function.update_of_ne (fun h ↦ hwRow ⟨_, h.symm⟩),
          Function.update_of_ne (fun h ↦ hwRow ⟨_, h.symm⟩)]
theorem hold1BitMap_eq_writeReg_of_zero {n : ℕ} (rCore : QRegister posCoreWires n)
    (rRow4 : QRegister 4 n) (j : Fin 18) {β : BitAssignment n}
    (hRow0 : ∀ r : Fin 4, β (rRow4 r) = 0) : hold1BitMap rCore rRow4 j β = p2d_writeReg β
    rRow4 (rowBit218 rCore j β ((shiftedPartnerSlotFast (fun w ↦ β (rCore w))).val % 64))
    := by
  dsimp only [hold1BitMap]
  refine congrArg (p2d_writeReg β rRow4) (funext fun r ↦ ?_)
  rw [hRow0 r, zero_add]
theorem subspaceStep_cLoad4Rows218Into {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mScr : ℕ} [NeZero (2 ^ n)] (hm : 75 ≤ mScr) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n) (rRow4 : QRegister 4 n)
    (hCS : rCore.DisjointWires rScr) (hBuf : RowBufDisj rCore rScr rRow4)
    {R : Operator (2 ^ n)}
    (hSupp : SupportedOn (fun β ↦ (∀ r : Fin 4, β (rRow4 r) = 0) ∧
      InvHoleBase218 hm rCore rScr β) R) :
    SubspaceStep (Var := Var) R ((uHold1Bit rCore rRow4 j hBuf.1).1 * R)
      (.circuit (cLoad4Rows218Into hm j rCore rScr rRow4 hCS hBuf)) := by
  refine subspaceStep_congr_out (subspaceStep_of_circuit R _)
    (hSupp _ _ fun β ⟨hRow0, hLo, _, hPar0, _⟩ ↦ ?_)
  have uKet : (uHold1Bit rCore rRow4 j hBuf.1).1.mulVec (ket β) =
      ket (hold1BitMap rCore rRow4 j β) := uHold1Bit_mulVec_ket rCore rRow4 j hBuf.1 β
  rw [cLoad4Rows218Into_eval_ket hm j rCore rScr rRow4 hCS hBuf β hRow0 hPar0
        ((shiftedPartnerSlotFast (fun w ↦ β (rCore w))).val % 64) (Nat.mod_lt _ (by decide)) hLo,
      uKet, hold1BitMap_eq_writeReg_of_zero rCore rRow4 j hRow0]
theorem supportedOn_loaded_of_uHold1Bit {n mScr : ℕ} (hm : 75 ≤ mScr) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n) (rRow4 : QRegister 4 n)
    (hBuf : RowBufDisj rCore rScr rRow4) {R : Operator (2 ^ n)} (hSupp : SupportedOn (fun β ↦
    (∀ r : Fin 4, β (rRow4 r) = 0) ∧ InvHoleBase218 hm rCore rScr β) R) : SupportedOn (fun α ↦
    (∀ r : Fin 4, α (rRow4 r) = rowBit218 rCore j α ((shiftedPartnerSlotFast (fun w ↦ α (rCore
    w))).val % 64) r) ∧ InvHoleBase218 hm rCore rScr α)
    ((uHold1Bit rCore rRow4 j hBuf.1).1 * R) := by
  refine supportedOn_unitary_mul (uHold1Bit rCore rRow4 j hBuf.1).1
    (hold1BitMap rCore rRow4 j) (uHold1Bit_mulVec_ket rCore rRow4 j hBuf.1) (fun β ⟨hRow0,
    hInv⟩ ↦ ⟨fun r ↦ ?_, hold1BitMap_preserves_invHoleBase218 hm rCore rScr rRow4 j hBuf
    hInv⟩) hSupp
  let α := hold1BitMap rCore rRow4 j β
  have hCore : (fun w ↦ α (rCore w)) = fun w ↦ β (rCore w) :=
    funext fun w ↦ p2d_writeReg_apply_of_not_mem _ _ _ _ fun ⟨r', hr'⟩ ↦ hBuf.1.ne w r' hr'.symm
  have hSlot : shiftedPartnerSlotFast (fun w ↦ α (rCore w)) =
      shiftedPartnerSlotFast (fun w ↦ β (rCore w)) := congrArg shiftedPartnerSlotFast hCore
  have hpw : posCoreWires = 4034 := rfl
  have hRowEq : rowBit218 rCore j α ((shiftedPartnerSlotFast (fun w ↦ α (rCore w))).val % 64) r =
      rowBit218 rCore j β ((shiftedPartnerSlotFast (fun w ↦ β (rCore w))).val % 64) r := by
    rw [hSlot]
    exact rowBit218_congr_elec rCore j
      (fun e ↦ p2d_writeReg_apply_of_not_mem _ _ _ _ fun ⟨r', hr'⟩ ↦
        hBuf.1.ne ⟨18 * e.val + j.val, by have := e.isLt; have := j.isLt; omega⟩ r' hr'.symm) _ r
  rw [hRowEq, hold1BitMap_eq_writeReg_of_zero rCore rRow4 j hRow0, p2d_writeReg_apply_reg]
/-- Zero-`T` CZ phase-fix circuit for a single `218`-slot anchored row (`W = 64`). -/
def cFixSingleRow218 {n mScr : ℕ} (hm : 75 ≤ mScr) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (r : Fin 4) : Circuit n :=
  let uLo : Fin 64 → Wire n := fun l ↦ rScr ⟨l.val, by omega⟩
  if hr3 : r.val < 3 then
    cFixRowAnchored1BitAux 64 64 (by decide) le_rfl uLo
      (rElecSlot rCore ⟨64 * r.val, by omega⟩ j)
      (fun i ↦ rElecSlot rCore ⟨64 * r.val + 1 + i.val, by omega⟩ j)
      (fun _ ↦ (rCore_ne_rSub hCS _ _ _).symm)
      (fun _ _ ↦ (rCore_ne_rSub hCS _ _ _).symm)
      64 le_rfl
  else
    cFixRowAnchored1BitAux 64 26 (by decide) (by decide) uLo
      (rElecSlot rCore ⟨192, by decide⟩ j)
      (fun i ↦ rElecSlot rCore ⟨193 + i.val, by omega⟩ j)
      (fun _ ↦ (rCore_ne_rSub hCS _ _ _).symm)
      (fun _ _ ↦ (rCore_ne_rSub hCS _ _ _).symm)
      64 le_rfl
theorem cFixSingleRow218_eval_ket {n mScr : ℕ} (hm : 75 ≤ mScr) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (r : Fin 4)
    (β : BitAssignment n) (l₀ : ℕ) (hl₀ : l₀ < 64)
    (hLo : ∀ l : Fin 64, β (rScr ⟨l.val, by omega⟩) = if l.val = l₀ then 1 else 0) :
    (cFixSingleRow218 hm j rCore rScr hCS r).eval.1.mulVec (ket β) =
      ((-1 : ℂ) ^ (rowBit218 rCore j β l₀ r).val) • ket β := by
  dsimp only [cFixSingleRow218, rowBit218]
  by_cases hr3 : r.val < 3
  · rw [dite_eq_left hr3, dite_eq_left hr3, dite_eq_left hl₀, cFixRowAnchored1BitAux_eval_ket]
    refine congrArg (fun z : ZMod 2 ↦ ((-1 : ℂ) ^ z.val) • ket β) ?_
    rw [Finset.sum_eq_single ⟨l₀, hl₀⟩]
    · rw [hLo ⟨l₀, hl₀⟩]; dsimp; rw [ite_eq_left rfl, one_mul]
      by_cases h0 : l₀ = 0
      · rw [dite_eq_left h0]
        exact congrArg (fun e ↦ β (rElecSlot rCore e j)) (Fin.ext (by dsimp; omega))
      · rw [dite_eq_right h0, dite_eq_left hl₀]
        exact congrArg (fun e ↦ β (rElecSlot rCore e j)) (Fin.ext (by dsimp; omega))
    · intro l _ hne
      rw [hLo l]; dsimp
      have hvne : l.val ≠ l₀ := fun hv ↦ hne (Fin.ext hv)
      rw [ite_eq_right hvne, zero_mul]
    · intro habs; exact absurd (Finset.mem_univ _) habs
  · rw [dite_eq_right hr3, dite_eq_right hr3, cFixRowAnchored1BitAux_eval_ket]
    refine congrArg (fun z : ZMod 2 ↦ ((-1 : ℂ) ^ z.val) • ket β) ?_
    rw [Finset.sum_eq_single ⟨l₀, hl₀⟩]
    · rw [hLo ⟨l₀, hl₀⟩]; dsimp; rw [ite_eq_left rfl, one_mul]
      by_cases h0 : l₀ = 0
      · rw [dite_eq_left h0, dite_eq_left (by omega : l₀ < 26)]
        exact congrArg (fun e ↦ β (rElecSlot rCore e j)) (Fin.ext (by dsimp; omega))
      · rw [dite_eq_right h0]
        by_cases hlt26 : l₀ < 26
        · rw [dite_eq_left hlt26, dite_eq_left hlt26]
          exact congrArg (fun e ↦ β (rElecSlot rCore e j)) (Fin.ext (by dsimp; omega))
        · rw [dite_eq_right hlt26, dite_eq_right hlt26]
    · intro l _ hne
      rw [hLo l]; dsimp
      have hvne : l.val ≠ l₀ := fun hv ↦ hne (Fin.ext hv)
      rw [ite_eq_right hvne, zero_mul]
    · intro habs; exact absurd (Finset.mem_univ _) habs
/-- Zero-`T` 4-row measurement-branch phase-fix circuit for the `218`-slot table. -/
def cBranchFix4Rows218Aux {n mScr : ℕ} (hm : 75 ≤ mScr) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (fRow : Fin 4 → Bool) :
    (k : ℕ) → (hk : k ≤ 4) → Circuit n
  | 0, _ => .identity
  | k + 1, hk =>
      let prev := cBranchFix4Rows218Aux hm j rCore rScr hCS fRow k (by omega)
      if fRow ⟨k, hk⟩ then
        prev ;;ᶜ cFixSingleRow218 hm j rCore rScr hCS ⟨k, hk⟩
      else
        prev
theorem cBranchFix4Rows218Aux_count_toff {n mScr : ℕ} (hm : 75 ≤ mScr) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (fRow : Fin 4 → Bool) :
    ∀ (k : ℕ) (hk : k ≤ 4),
      (cBranchFix4Rows218Aux hm j rCore rScr hCS fRow k hk).count TOFF = 0
  | 0, _ => rfl
  | k + 1, hk => by
      dsimp only [cBranchFix4Rows218Aux]
      by_cases hf : fRow ⟨k, hk⟩
      · rw [ite_eq_left hf, Circuit.count_seq,
            cBranchFix4Rows218Aux_count_toff hm j rCore rScr hCS fRow k]
        dsimp only [cFixSingleRow218]
        by_cases hr3 : k < 3
        · rw [dite_eq_left hr3, cFixRowAnchored1BitAux_count_toff]
        · rw [dite_eq_right hr3, cFixRowAnchored1BitAux_count_toff]
      · rw [ite_eq_right hf]
        exact cBranchFix4Rows218Aux_count_toff hm j rCore rScr hCS fRow k (by omega)
theorem cBranchFix4Rows218Aux_count_t {n mScr : ℕ} (hm : 75 ≤ mScr) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (fRow : Fin 4 → Bool) :
    ∀ (k : ℕ) (hk : k ≤ 4),
      (cBranchFix4Rows218Aux hm j rCore rScr hCS fRow k hk).count T = 0
  | 0, _ => rfl
  | k + 1, hk => by
      dsimp only [cBranchFix4Rows218Aux]
      by_cases hf : fRow ⟨k, hk⟩
      · rw [ite_eq_left hf, Circuit.count_seq,
            cBranchFix4Rows218Aux_count_t hm j rCore rScr hCS fRow k]
        dsimp only [cFixSingleRow218]
        by_cases hr3 : k < 3
        · rw [dite_eq_left hr3, cFixRowAnchored1BitAux_count_t]
        · rw [dite_eq_right hr3, cFixRowAnchored1BitAux_count_t]
      · rw [ite_eq_right hf]
        exact cBranchFix4Rows218Aux_count_t hm j rCore rScr hCS fRow k (by omega)
theorem cBranchFix4Rows218Aux_eval_ket {n mScr : ℕ} (hm : 75 ≤ mScr) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (fRow : Fin 4 → Bool)
    (β : BitAssignment n) (l₀ : ℕ) (hl₀ : l₀ < 64)
    (hLo : ∀ l : Fin 64, β (rScr ⟨l.val, by omega⟩) = if l.val = l₀ then 1 else 0) :
    ∀ (k : ℕ) (hk : k ≤ 4),
      (cBranchFix4Rows218Aux hm j rCore rScr hCS fRow k hk).eval.1.mulVec (ket β) =
        (∏ r : Fin k,
          if fRow ⟨r.val, by omega⟩ then
            (-1 : ℂ) ^ (rowBit218 rCore j β l₀ ⟨r.val, by omega⟩).val
          else 1) • ket β
  | 0, _ => by simp [cBranchFix4Rows218Aux]
  | k + 1, hk => by
      dsimp only [cBranchFix4Rows218Aux]
      by_cases hf : fRow ⟨k, hk⟩
      · rw [ite_eq_left hf, eval_seq_mulVec,
            cBranchFix4Rows218Aux_eval_ket hm j rCore rScr hCS fRow β l₀ hl₀ hLo k (by omega),
            Matrix.mulVec_smul, cFixSingleRow218_eval_ket hm j rCore rScr hCS ⟨k, hk⟩ β l₀ hl₀ hLo,
            smul_smul, Fin.prod_univ_castSucc]
        dsimp only [Fin.val_last, Fin.val_castSucc]
        rw [ite_eq_left hf]
      · rw [ite_eq_right hf,
            cBranchFix4Rows218Aux_eval_ket hm j rCore rScr hCS fRow β l₀ hl₀ hLo k (by omega),
            Fin.prod_univ_castSucc]
        dsimp only [Fin.val_last, Fin.val_castSucc]
        rw [ite_eq_right hf, mul_one]
/-- `8 T`, `TOFF = 0` row-select + CZ phase kick + 1-wire MBU from any 4-row buffer `rRow4`
(leaving `rRow4` intact!). -/
noncomputable def dSelectKickFrom4Rows {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr) (v : Var)
    (j : Fin 18) {rCore : QRegister posCoreWires n} (rMeas : QRegister 18 n)
    (rScr : QRegister mScr n) (rRow4 : QRegister 4 n) (hMS : rMeas.DisjointWires rScr)
    (hBuf : RowBufDisj rCore rScr rRow4) : DynamicCircuit Var n :=
  let uHi : Fin 4 → Wire n := fun h ↦ rScr ⟨64 + h.val, by omega⟩
  let rSel1 : QRegister 1 n := p2dSubReg rScr 74 1 (by omega)
  let wSel : Wire n := rScr ⟨74, by omega⟩
  let cSel := cLoadRowAnchored1Bit 4 4 (by decide) le_rfl uHi (uHi 0)
    (rRow4 ⟨0, by decide⟩) (fun i ↦ rRow4 ⟨1 + i.val, by omega⟩) wSel
    (fun _ ↦ rRow4.wires.injective.ne (Fin.ne_of_val_ne (by dsimp; omega)))
    (fun _ ↦ (hBuf.2 ⟨74, by omega⟩ _ (Or.inr (by dsimp; omega))).symm)
    ((hBuf.2 ⟨74, by omega⟩ _ (Or.inr (by dsimp; omega))).symm)
    (fun _ ↦ rSub_ne_of_ne rScr (by omega) (by omega) (by omega))
    (rSub_ne_of_ne rScr (by omega) (by omega) (by omega))
  let cCz := czCircuit wSel (rMeas j) (hMS.ne j ⟨74, by omega⟩).symm
  let cFixSel : Circuit n :=
    cFixRowAnchored1BitAux 4 4 (by decide) le_rfl uHi
      (rRow4 ⟨0, by decide⟩) (fun i ↦ rRow4 ⟨1 + i.val, by omega⟩)
      (fun h ↦ hBuf.2 ⟨64 + h.val, by omega⟩ _ (Or.inl (by dsimp; omega)))
      (fun h _ ↦ hBuf.2 ⟨64 + h.val, by omega⟩ _ (Or.inl (by dsimp; omega)))
      4 le_rfl
  .seq (.circuit (cSel ;;ᶜ cCz))
    (DynCircuitExt.measureXResetAndBranch v 1 rSel1
      (fun fSel ↦ .circuit (if fSel 0 then cFixSel else .identity)))
theorem dSelectKickFrom4Rows_count_toff {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr)
    (v : Var) (j : Fin 18) {rCore : QRegister posCoreWires n}
    (rMeas : QRegister 18 n) (rScr : QRegister mScr n) (rRow4 : QRegister 4 n)
    (hMS : rMeas.DisjointWires rScr) (hBuf : RowBufDisj rCore rScr rRow4) :
    (dSelectKickFrom4Rows hm v j rMeas rScr rRow4 hMS hBuf).count TOFF = 0 := by
  dsimp only [dSelectKickFrom4Rows, DynamicCircuit.count]
  rw [Circuit.count_seq, cLoadRowAnchored1Bit_count_toff, czCircuit_count_toff]
  have h1 : (DynCircuitExt.measureXResetAndBranch (Var := Var) v 1 (p2dSubReg rScr 74 1 hm)
      (fun fSel ↦ .circuit (if fSel 0 then
        cFixRowAnchored1BitAux 4 4 (by decide) le_rfl
          (fun h : Fin 4 ↦ rScr ⟨64 + h.val, by omega⟩)
          (rRow4 ⟨0, by decide⟩) (fun i ↦ rRow4 ⟨1 + i.val, by omega⟩)
          (fun h ↦ hBuf.2 ⟨64 + h.val, by omega⟩ _ (Or.inl (by dsimp; omega)))
          (fun h _ ↦ hBuf.2 ⟨64 + h.val, by omega⟩ _ (Or.inl (by dsimp; omega))) 4 le_rfl
       else .identity))).count TOFF = 0 :=
    Nat.le_zero.mp (DynCircuitExt.count_measureXResetAndBranch_TOFF_le v 1 _ _ 0 fun fSel ↦ by
      cases fSel 0 <;> simp [DynamicCircuit.count, cFixRowAnchored1BitAux_count_toff])
  rw [h1]
theorem dSelectKickFrom4Rows_count_t {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr)
    (v : Var) (j : Fin 18) {rCore : QRegister posCoreWires n}
    (rMeas : QRegister 18 n) (rScr : QRegister mScr n) (rRow4 : QRegister 4 n)
    (hMS : rMeas.DisjointWires rScr) (hBuf : RowBufDisj rCore rScr rRow4) :
    (dSelectKickFrom4Rows hm v j rMeas rScr rRow4 hMS hBuf).count T = 8 := by
  dsimp only [dSelectKickFrom4Rows, DynamicCircuit.count]
  rw [Circuit.count_seq, cLoadRowAnchored1Bit_count_t, czCircuit_count_t]
  have h1 : (DynCircuitExt.measureXResetAndBranch (Var := Var) v 1 (p2dSubReg rScr 74 1 hm)
      (fun fSel ↦ .circuit (if fSel 0 then
        cFixRowAnchored1BitAux 4 4 (by decide) le_rfl
          (fun h : Fin 4 ↦ rScr ⟨64 + h.val, by omega⟩)
          (rRow4 ⟨0, by decide⟩) (fun i ↦ rRow4 ⟨1 + i.val, by omega⟩)
          (fun h ↦ hBuf.2 ⟨64 + h.val, by omega⟩ _ (Or.inl (by dsimp; omega)))
          (fun h _ ↦ hBuf.2 ⟨64 + h.val, by omega⟩ _ (Or.inl (by dsimp; omega))) 4 le_rfl
       else .identity))).count T = 0 :=
    Nat.le_zero.mp (DynCircuitExt.count_measureXResetAndBranch_T_le v 1 _ _ 0 fun fSel ↦ by
      cases fSel 0 <;> simp [DynamicCircuit.count, cFixRowAnchored1BitAux_count_t])
  rw [h1]
theorem subspaceStep_dSelectKickFrom4Rows {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mScr : ℕ} [NeZero (2 ^ n)] (hm : 75 ≤ mScr) (v : Var) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) (rScr : QRegister mScr n)
    (rRow4 : QRegister 4 n) (hMS : rMeas.DisjointWires rScr)
    (hBuf : RowBufDisj rCore rScr rRow4) {R : Operator (2 ^ n)} (hSupp : SupportedOn (fun α ↦
    (∀ r : Fin 4, α (rRow4 r) = rowBit218 rCore j α ((shiftedPartnerSlotFast (fun w ↦ α (rCore
    w))).val % 64) r) ∧ InvHoleBase218 hm rCore rScr α) R) : SubspaceStep R
    ((uKick1Bit218 j rCore rMeas).1 * R)
    (dSelectKickFrom4Rows hm v j rMeas rScr rRow4 hMS hBuf) := by
  let uHi : Fin 4 → Wire n := fun h ↦ rScr ⟨64 + h.val, by omega⟩
  let rSel1 : QRegister 1 n := p2dSubReg rScr 74 1 (by omega)
  let wSel : Wire n := rScr ⟨74, by omega⟩
  let cSel := cLoadRowAnchored1Bit 4 4 (by decide) le_rfl uHi (uHi 0)
    (rRow4 ⟨0, by decide⟩) (fun i ↦ rRow4 ⟨1 + i.val, by omega⟩) wSel
    (fun _ ↦ rRow4.wires.injective.ne (Fin.ne_of_val_ne (by dsimp; omega)))
    (fun _ ↦ (hBuf.2 ⟨74, by omega⟩ _ (Or.inr (by dsimp; omega))).symm)
    ((hBuf.2 ⟨74, by omega⟩ _ (Or.inr (by dsimp; omega))).symm)
    (fun _ ↦ rSub_ne_of_ne rScr (by omega) (by omega) (by omega))
    (rSub_ne_of_ne rScr (by omega) (by omega) (by omega))
  let cCz := czCircuit wSel (rMeas j) (hMS.ne j ⟨74, by omega⟩).symm
  let cFixSel : Circuit n :=
    cFixRowAnchored1BitAux 4 4 (by decide) le_rfl uHi
      (rRow4 ⟨0, by decide⟩) (fun i ↦ rRow4 ⟨1 + i.val, by omega⟩)
      (fun h ↦ hBuf.2 ⟨64 + h.val, by omega⟩ _ (Or.inl (by dsimp; omega)))
      (fun h _ ↦ hBuf.2 ⟨64 + h.val, by omega⟩ _ (Or.inl (by dsimp; omega)))
      4 le_rfl
  have hSel1_0 : rSel1 0 = wSel := congrArg rScr.wires (Fin.ext (by dsimp [rSel1, p2dSubReg]))
  refine subspaceStep_seq_measureXReset v rSel1
    (subspaceStep_of_circuit R (cSel ;;ᶜ cCz)) (fun fSel ↦ ?_)
  refine subspaceStep_congr_out
    (subspaceStep_of_circuit _ (if fSel 0 then cFixSel else .identity)) ?_
  rw [show ((((√(1 / 2)) ^ 1 : ℝ) : ℂ) • ((uKick1Bit218 j rCore rMeas).1 * R)) =
      ((((√(1 / 2)) ^ 1 : ℝ) : ℂ) • (uKick1Bit218 j rCore rMeas).1) * R by
        rw [Matrix.smul_mul],
      ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  refine hSupp _ _ fun α ⟨hRow, _, hHi, _, hSel0⟩ ↦ ?_
  let s₀ := shiftedPartnerSlotFast (fun w ↦ α (rCore w))
  have hh₀ : s₀.val / 64 < 4 := by have := s₀.isLt; omega
  let vals := rowBit218 rCore j α (s₀.val % 64)
  let actVal := vals ⟨s₀.val / 64, hh₀⟩
  have hBnd : α (uHi 0) = if (s₀.val / 64 = 0 ∨ 4 ≤ s₀.val / 64) then 1 else 0 := by
    rw [hHi 0]; dsimp
    by_cases h0 : s₀.val / 64 = 0
    · rw [ite_eq_left h0.symm, ite_eq_left (Or.inl h0)]
    · rw [ite_eq_right (Ne.symm h0), ite_eq_right (by omega)]
  have hSelKet : cSel.eval.1.mulVec (ket α) = ket (Function.update α wSel actVal) := by
    rw [cLoadRowAnchored1Bit_eval_ket 4 4 (by decide) le_rfl uHi (uHi 0)
      (rRow4 ⟨0, by decide⟩) (fun i ↦ rRow4 ⟨1 + i.val, by omega⟩) wSel _ _ _ _ _
      (fun i₁ i₂ h ↦ Fin.ext (by
        have := congrArg Fin.val (rRow4.wires.injective h); dsimp at this; omega))
      (fun h _ ↦ hBuf.2 ⟨64 + h.val, by omega⟩ _ (Or.inl (by dsimp; omega)))
      (fun _ ↦ hBuf.2 ⟨64, by omega⟩ _ (Or.inl (by dsimp; omega)))
      α hSel0 (s₀.val / 64) hh₀ hHi hBnd]
    refine congrArg (fun b ↦ ket (Function.update α wSel b)) ?_
    by_cases h0 : s₀.val / 64 = 0
    · rw [dite_eq_left h0, hRow ⟨0, by decide⟩]
      exact congrArg vals (Fin.ext (by dsimp; omega))
    · rw [dite_eq_right h0, dite_eq_left hh₀, hRow ⟨1 + (s₀.val / 64 - 1), by omega⟩]
      exact congrArg vals (Fin.ext (by dsimp; omega))
  have hActEq : actVal = α (rElecSlot rCore s₀ j) := rowBit218_at_active rCore j α s₀
  have hResetSel : p2d_writeReg (Function.update α wSel actVal) rSel1 (fun _ ↦ 0) = α := by
    funext w
    by_cases hw : w = wSel
    · subst hw; rw [← hSel1_0, p2d_writeReg_apply_reg, hSel1_0, hSel0]
    · rw [p2d_writeReg_apply_of_not_mem _ _ _ _
            (fun ⟨t, ht⟩ ↦ by fin_cases t; exact hw (ht.symm.trans hSel1_0)),
          Function.update_of_ne hw]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      eval_seq_mulVec, hSelKet, ket_czCircuit, Function.update_self,
      Function.update_of_ne (hMS.ne j ⟨74, by omega⟩),
      Matrix.mulVec_smul, p2d_xResetKraus_mulVec_ket, Fin.prod_univ_one,
      hSel1_0, Function.update_self, hResetSel, hActEq, smul_smul, Matrix.mulVec_smul,
      Matrix.smul_mulVec, uKick1Bit218_mulVec_ket, smul_smul]
  cases hf0 : fSel 0
  · simp only [Bool.false_eq_true, ↓reduceIte, Circuit.eval_identity,
      OneMemClass.coe_one, Matrix.one_mulVec, mul_one]
    exact congrArg (· • ket α) (mul_comm _ _)
  · simp only [↓reduceIte]
    rw [cFixRowAnchored1Bit_eval_ket 4 4 (by decide) le_rfl uHi
          (rRow4 ⟨0, by decide⟩) (fun i ↦ rRow4 ⟨1 + i.val, by omega⟩) _ _
          α (s₀.val / 64) hh₀ hHi, smul_smul]
    have hFixVal : (if h0 : s₀.val / 64 = 0 then α (rRow4 ⟨0, by decide⟩)
        else if hlt : s₀.val / 64 < 4 then α (rRow4 ⟨1 + (s₀.val / 64 - 1), by omega⟩)
        else α (rRow4 ⟨0, by decide⟩)) = actVal := by
      by_cases h0 : s₀.val / 64 = 0
      · rw [dite_eq_left h0, hRow ⟨0, by decide⟩]
        exact congrArg vals (Fin.ext (by dsimp; omega))
      · rw [dite_eq_right h0, dite_eq_left hh₀, hRow ⟨1 + (s₀.val / 64 - 1), by omega⟩]
        exact congrArg vals (Fin.ext (by dsimp; omega))
    rw [hFixVal, hActEq]
    refine congrArg (· • ket α) ?_
    have hSq : (-1 : ℂ) ^ (α (rElecSlot rCore s₀ j)).val *
        (-1 : ℂ) ^ (α (rElecSlot rCore s₀ j)).val = 1 := by
      rcases bit_cases (α (rElecSlot rCore s₀ j)) with hvx | hvx <;> simp [hvx]
    dsimp only [s₀] at hSq ⊢
    linear_combination
      (((√(1 / 2)) ^ 1 : ℝ) : ℂ) *
        (-1 : ℂ) ^ (α (rElecSlot rCore (shiftedPartnerSlotFast (fun w ↦ α (rCore w))) j) *
          α (rMeas j)).val * hSq
/-- `0 T`, `TOFF = 0` 4-wire MBU uncompute of `rRow4` with classical CZ row-phase fixup. -/
noncomputable def dUncompute4Rows218 {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr) (v : Var)
    (j : Fin 18) (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (rRow4 : QRegister 4 n) (hCS : rCore.DisjointWires rScr) : DynamicCircuit Var n :=
    DynCircuitExt.measureXResetAndBranch v 4 rRow4 (fun fRow ↦ .circuit
    (cBranchFix4Rows218Aux hm j rCore rScr hCS fRow 4 le_rfl))
theorem dUncompute4Rows218_count_toff {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr)
    (v : Var) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n) (rRow4 : QRegister 4 n)
    (hCS : rCore.DisjointWires rScr) :
    (dUncompute4Rows218 (Var := Var) hm v j rCore rScr rRow4 hCS).count TOFF = 0 :=
  Nat.le_zero.mp (DynCircuitExt.count_measureXResetAndBranch_TOFF_le v 4 _ _ 0 fun fRow ↦ by
    simp [DynamicCircuit.count, cBranchFix4Rows218Aux_count_toff])
theorem dUncompute4Rows218_count_t {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr)
    (v : Var) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n) (rRow4 : QRegister 4 n)
    (hCS : rCore.DisjointWires rScr) :
    (dUncompute4Rows218 (Var := Var) hm v j rCore rScr rRow4 hCS).count T = 0 :=
  Nat.le_zero.mp (DynCircuitExt.count_measureXResetAndBranch_T_le v 4 _ _ 0 fun fRow ↦ by
    simp [DynamicCircuit.count, cBranchFix4Rows218Aux_count_t])
theorem subspaceStep_dUncompute4Rows218 {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mScr : ℕ} [NeZero (2 ^ n)] (hm : 75 ≤ mScr) (v : Var) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n) (rRow4 : QRegister 4 n)
    (hCS : rCore.DisjointWires rScr) (hCR : rCore.DisjointWires rRow4) {R : Operator (2 ^ n)}
    (hSupp : SupportedOn (fun β ↦ (∀ r : Fin 4, β (rRow4 r) = 0) ∧ InvHoleBase218 hm rCore
    rScr β) R) : SubspaceStep ((uHold1Bit rCore rRow4 j hCR).1 * R) R
    (dUncompute4Rows218 hm v j rCore rScr rRow4 hCS) := by
  refine subspaceStep_measureXReset v rRow4 fun fRow ↦ ?_
  refine subspaceStep_congr_out
    (subspaceStep_of_circuit _ (cBranchFix4Rows218Aux hm j rCore rScr hCS fRow 4 le_rfl)) ?_
  rw [show ((((√(1 / 2)) ^ 4 : ℝ) : ℂ) • R) =
      ((((√(1 / 2)) ^ 4 : ℝ) : ℂ) • (1 : Operator (2 ^ n))) * R by
        rw [Matrix.smul_mul, Matrix.one_mul],
      ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  refine hSupp _ _ fun β ⟨hRow0, hLo, _, _, _⟩ ↦ ?_
  let s₀ := shiftedPartnerSlotFast (fun w ↦ β (rCore w))
  have hl₀ : s₀.val % 64 < 64 := Nat.mod_lt _ (by decide)
  let vals := rowBit218 rCore j β (s₀.val % 64)
  have hKetH : (uHold1Bit rCore rRow4 j hCR).1.mulVec (ket β) = ket (p2d_writeReg β rRow4 vals) :=
    (uHold1Bit_mulVec_ket rCore rRow4 j hCR β).trans
      (congrArg ket (hold1BitMap_eq_writeReg_of_zero rCore rRow4 j hRow0))
  rw[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hKetH, p2d_xResetKraus_mulVec_ket]
  simp only [p2d_writeReg_apply_reg]
  rw [p2d_writeReg_reset_zero_of_zero β rRow4 vals hRow0,
      Matrix.mulVec_smul,
      cBranchFix4Rows218Aux_eval_ket hm j rCore rScr hCS fRow β (s₀.val % 64) hl₀ hLo 4 le_rfl,
      smul_smul, Matrix.smul_mulVec, Matrix.one_mulVec]
  refine congrArg (· • ket β) ?_
  have hProdSq : (∏ b : Fin 4, if fRow b then (-1 : ℂ) ^ (vals b).val else 1) *
      (∏ r : Fin 4, if fRow ⟨r.val, by omega⟩ then
        (-1 : ℂ) ^ (vals ⟨r.val, by omega⟩).val else 1) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun b _ ↦ ?_
    have hbEq : (⟨b.val, by omega⟩ : Fin 4) = b := Fin.ext rfl
    rw [hbEq]
    by_cases hfb : fRow b
    · rw [ite_eq_left hfb]
      rcases bit_cases (vals b) with hvx | hvx <;> simp [hvx]
    · simp [hfb]
  linear_combination ((((√(1 / 2)) ^ 4 : ℝ) : ℂ)) * hProdSq
theorem uHold1Bit_comm_uKick1Bit218 {n : ℕ}
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) (rRow4 : QRegister 4 n)
    (j₁ j₂ : Fin 18) (hCR : rCore.DisjointWires rRow4) (hMR : rMeas.DisjointWires rRow4) :
    uHold1Bit rCore rRow4 j₁ hCR * uKick1Bit218 j₂ rCore rMeas =
      uKick1Bit218 j₂ rCore rMeas * uHold1Bit rCore rRow4 j₁ hCR := by
  apply Subtype.ext; apply matrix_ext_ket; intro β
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      uKick1Bit218_mulVec_ket, Matrix.mulVec_smul, uHold1Bit_mulVec_ket, uKick1Bit218_mulVec_ket]
  let α := hold1BitMap rCore rRow4 j₁ β
  have hCore : (fun w ↦ α (rCore w)) = fun w ↦ β (rCore w) :=
    funext fun w ↦ p2d_writeReg_apply_of_not_mem _ _ _ _ fun ⟨r, hr⟩ ↦ hCR.ne w r hr.symm
  have hSlot : shiftedPartnerSlotFast (fun w ↦ α (rCore w)) =
      shiftedPartnerSlotFast (fun w ↦ β (rCore w)) := congrArg shiftedPartnerSlotFast hCore
  have hE : ∀ e : Fin 218, α (rElecSlot rCore e j₂) = β (rElecSlot rCore e j₂) :=
    fun e ↦ p2d_writeReg_apply_of_not_mem _ _ _ _ fun ⟨r, hr⟩ ↦ by
      simp only [rElecSlot, QRegister.slice_apply] at hr
      exact hCR.ne _ r hr.symm
  have hM : α (rMeas j₂) = β (rMeas j₂) :=
    p2d_writeReg_apply_of_not_mem _ _ _ _ fun ⟨r, hr⟩ ↦ hMR.ne j₂ r hr.symm
  dsimp only [α] at hSlot hE hM
  dsimp only
  rw [hSlot, hE, hM]
theorem uKickPrefix218_zero {n : ℕ} (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) :
    uKickPrefix218 0 (Nat.zero_le 18) rCore rMeas = 1 := by
  dsimp only [uKickPrefix218]
  exact diagSignUnitary_false
theorem uKickPrefix218_succ {n : ℕ} (k : ℕ) (hk : k + 1 ≤ 18)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) :
    uKickPrefix218 (k + 1) hk rCore rMeas =
      uKick1Bit218 ⟨k, hk⟩ rCore rMeas * uKickPrefix218 k (by omega) rCore rMeas := by
  apply Subtype.ext; apply matrix_ext_ket; intro β
  dsimp only [uKickPrefix218]
  rw[Submonoid.coe_mul, ← Matrix.mulVec_mulVec, diagSignUnitary_mulVec_ket,
      diagSignUnitary_mulVec_ket, Matrix.mulVec_smul, uKick1Bit218_mulVec_ket, smul_smul]
  have hβ : basisBits n ((basisBitsEquiv n).symm β) = β := (basisBitsEquiv n).apply_symm_apply β
  simp only [hβ, ite_decide_eq_one_zmod2, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
  rw [neg_one_pow_zmod2_add, mul_comm]
/-- Single-bit (`436 + 8 = 444 T`) `218`-slot unheld phase-kick dynamic circuit at `.hole`. -/
noncomputable def dKick1Bit218 {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr)
    (v : Var) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) : DynamicCircuit Var n :=
  let rRow70 := p2dSubReg rScr 70 4 (by omega)
  let hBuf := rowBufDisj_scr70 hm rCore rScr hCS
  .seq (.circuit (cLoad4Rows218Into hm j rCore rScr rRow70 hCS hBuf))
    (.seq (dSelectKickFrom4Rows hm v j rMeas rScr rRow70 hMS hBuf)
          (dUncompute4Rows218 hm v j rCore rScr rRow70 hCS))
theorem dKick1Bit218_count_toff {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr)
    (v : Var) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) :
    (dKick1Bit218 (Var := Var) hm v j rCore rMeas rScr hCS hMS).count TOFF = 0 := by
  dsimp only [dKick1Bit218, DynamicCircuit.count]
  rw [cLoad4Rows218Into_count_toff, dSelectKickFrom4Rows_count_toff, dUncompute4Rows218_count_toff]
theorem dKick1Bit218_count_t {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr)
    (v : Var) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) :
    (dKick1Bit218 (Var := Var) hm v j rCore rMeas rScr hCS hMS).count T = 444 := by
  dsimp only [dKick1Bit218, DynamicCircuit.count]
  rw [cLoad4Rows218Into_count_t, dSelectKickFrom4Rows_count_t, dUncompute4Rows218_count_t]
theorem subspaceStep_dKick1Bit218 {Var : Type} [Fintype Var] [DecidableEq Var] {n mScr : ℕ}
    [NeZero (2 ^ n)] (hm : 75 ≤ mScr) (v : Var) (j : Fin 18)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) {R : Operator (2 ^ n)}
    (hSupp : SupportedOn (InvHoleShifted218 hm rCore rScr) R) : SubspaceStep R
    ((uKick1Bit218 j rCore rMeas).1 * R) (dKick1Bit218 hm v j rCore rMeas rScr hCS hMS) := by
  let rRow70 := p2dSubReg rScr 70 4 (by omega)
  let hBuf := rowBufDisj_scr70 hm rCore rScr hCS
  have hMR70 : rMeas.DisjointWires rRow70 := by
    rw [QRegister.disjoint_iff]; intro i r h
    have hr : rRow70 r = rScr ⟨70 + r.val, by omega⟩ :=
      congrArg rScr.wires (Fin.ext (by dsimp [rRow70, p2dSubReg]))
    exact hMS.ne i ⟨70 + r.val, by omega⟩ (h.trans hr)
  have hSuppBase : SupportedOn (fun β ↦ (∀ r : Fin 4, β (rRow70 r) = 0) ∧
      InvHoleBase218 hm rCore rScr β) R :=
    supportedOn_mono (fun β h ↦ (invHoleShifted218_iff_base hm rCore rScr β).mp h) hSupp
  have s1 := subspaceStep_cLoad4Rows218Into (Var := Var) hm j rCore rScr rRow70 hCS hBuf hSuppBase
  have s2 := subspaceStep_dSelectKickFrom4Rows hm v j rCore rMeas rScr rRow70 hMS hBuf
    (supportedOn_loaded_of_uHold1Bit hm j rCore rScr rRow70 hBuf hSuppBase)
  have hComm : (uKick1Bit218 j rCore rMeas).1 * ((uHold1Bit rCore rRow70 j hBuf.1).1 * R) =
      (uHold1Bit rCore rRow70 j hBuf.1).1 * ((uKick1Bit218 j rCore rMeas).1 * R) := by
    rw [← Matrix.mul_assoc, ← Submonoid.coe_mul,
        ← uHold1Bit_comm_uKick1Bit218 rCore rMeas rRow70 j j hBuf.1 hMR70,
        Submonoid.coe_mul, Matrix.mul_assoc]
  have hSuppKick : SupportedOn (fun β ↦ (∀ r : Fin 4, β (rRow70 r) = 0) ∧
      InvHoleBase218 hm rCore rScr β) ((uKick1Bit218 j rCore rMeas).1 * R) :=
    supportedOn_diagSignUnitary_mul _ hSuppBase
  have s3 := subspaceStep_dUncompute4Rows218 hm v j rCore rScr rRow70 hCS hBuf.1 hSuppKick
  exact s1.seq ((subspaceStep_congr_out s2 hComm).seq s3)
/-- `k`-bit unheld phase-kick prefix at `.hole` (`444 * k` `T`). -/
noncomputable def dPhaseKickHole218Aux {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr)
    (v : Var) (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) :
    ∀ (k : ℕ), k ≤ 18 → DynamicCircuit Var n
  | 0, _ => .circuit .identity
  | k + 1, hk =>
      .seq (dPhaseKickHole218Aux hm v rCore rMeas rScr hCS hMS k (by omega))
           (dKick1Bit218 hm v ⟨k, hk⟩ rCore rMeas rScr hCS hMS)
noncomputable def dPhaseKickHole218 {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr)
    (v : Var) (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) : DynamicCircuit Var n :=
  dPhaseKickHole218Aux hm v rCore rMeas rScr hCS hMS 18 le_rfl
theorem dPhaseKickHole218Aux_count {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr)
    (v : Var) (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) :
    ∀ (k : ℕ) (hk : k ≤ 18),
      (dPhaseKickHole218Aux (Var := Var) hm v rCore rMeas rScr hCS hMS k hk).count TOFF = 0 ∧
      (dPhaseKickHole218Aux (Var := Var) hm v rCore rMeas rScr hCS hMS k hk).count T = 444 * k
  | 0, _ => ⟨rfl, rfl⟩
  | k + 1, hk => by
      dsimp only [dPhaseKickHole218Aux, DynamicCircuit.count]
      obtain ⟨h1, h2⟩ := dPhaseKickHole218Aux_count hm v rCore rMeas rScr hCS hMS k (by omega)
      rw [h1, h2, dKick1Bit218_count_toff, dKick1Bit218_count_t]
      exact ⟨rfl, by omega⟩
theorem subspaceStep_dPhaseKickHole218Aux {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mScr : ℕ} [NeZero (2 ^ n)] (hm : 75 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) :
    ∀ (k : ℕ) (hk : k ≤ 18) {R : Operator (2 ^ n)},
      SupportedOn (InvHoleShifted218 hm rCore rScr) R →
      SubspaceStep R ((uKickPrefix218 k hk rCore rMeas).1 * R)
        (dPhaseKickHole218Aux hm v rCore rMeas rScr hCS hMS k hk)
  | 0, hk, R, _ => by
      dsimp only [dPhaseKickHole218Aux]
      rw [uKickPrefix218_zero]
      exact subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) R .identity) (by simp)
  | k + 1, hk, R, hSupp => by
      dsimp only [dPhaseKickHole218Aux]
      have sPrev := subspaceStep_dPhaseKickHole218Aux hm v rCore rMeas rScr hCS hMS k (by omega)
          hSupp
      have hSuppPrev : SupportedOn (InvHoleShifted218 hm rCore rScr)
          ((uKickPrefix218 k (by omega) rCore rMeas).1 * R) :=
        supportedOn_diagSignUnitary_mul _ hSupp
      have sLast := subspaceStep_dKick1Bit218 hm v ⟨k, hk⟩ rCore rMeas rScr hCS hMS hSuppPrev
      refine subspaceStep_congr_out (sPrev.seq sLast) ?_
      rw [uKickPrefix218_succ, Submonoid.coe_mul, Matrix.mul_assoc]
/-- `18`-bit shifted-partner load at `.hole` (`7,992 T`, `TOFF = 0`). -/
noncomputable def dLoadHole218 {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr)
    (v : Var) (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) : DynamicCircuit Var n :=
  .seq (.circuit (cHadReg rMeas))
    (.seq (dPhaseKickHole218 hm v rCore rMeas rScr hCS hMS) (.circuit (cHadReg rMeas)))
theorem dLoadHole218_count {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr)
    (v : Var) (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) :
    (dLoadHole218 (Var := Var) hm v rCore rMeas rScr hCS hMS).count TOFF = 0 ∧
    (dLoadHole218 (Var := Var) hm v rCore rMeas rScr hCS hMS).count T = 7992 := by
  dsimp only [dLoadHole218, dPhaseKickHole218, DynamicCircuit.count]
  obtain ⟨h1, h2⟩ := dPhaseKickHole218Aux_count (Var := Var) hm v rCore rMeas rScr hCS hMS 18 le_rfl
  rw [cHadReg_count_toff, cHadReg_count_t, h1, h2]
  exact ⟨rfl, rfl⟩
theorem subspaceStep_dLoadHole218 {Var : Type} [Fintype Var] [DecidableEq Var]
    {n kData mScr : ℕ} [NeZero (2 ^ n)] (hm : 75 ≤ mScr) (v : Var) (rData : QRegister kData n)
    (selCore : QRegister posCoreWires kData) (rMeas : QRegister 18 n)
    (rScr : QRegister mScr n) (hDM : rData.DisjointWires rMeas)
    (hCS : (rData.compose selCore).DisjointWires rScr) (hMS : rMeas.DisjointWires rScr)
    {R : Operator (2 ^ n)} (hSupp : SupportedOn (InvHoleShifted218 hm (rData.compose selCore)
    rScr) R) : SubspaceStep R (((rData.concat rMeas hDM).embedUnitary (uLensLoad
    (shiftedPartnerLens218 selCore))).1 * R)
    (dLoadHole218 hm v (rData.compose selCore) rMeas rScr hCS hMS) := by
  let rCore := rData.compose selCore
  have hCM : rCore.DisjointWires rMeas := hDM.compose_left selCore
  have hInvM : ∀ β₁ β₂ : BitAssignment n, (∀ w, (∀ j : Fin 18, w ≠ rMeas j) → β₁ w = β₂ w) →
      (InvHoleShifted218 hm rCore rScr β₁ ↔ InvHoleShifted218 hm rCore rScr β₂) :=
    fun β₁ β₂ h ↦ by
      have hCore : (fun w ↦ β₁ (rCore w)) = fun w ↦ β₂ (rCore w) :=
        funext fun w ↦ h (rCore w) fun j ↦ hCM.ne w j
      have hS : ∀ k : Fin mScr, β₁ (rScr k) = β₂ (rScr k) :=
        fun k ↦ h (rScr k) fun j ↦ (hMS.ne j k).symm
      have hSub : ∀ r : Fin 4,
          β₁ (p2dSubReg rScr 70 4 (by omega) r) = β₂ (p2dSubReg rScr 70 4 (by omega) r) :=
        fun r ↦ hS ⟨70 + r.val, by omega⟩
      dsimp only [InvHoleShifted218]
      simp only [hCore, hS, hSub]
  have s1 := subspaceStep_of_circuit (Var := Var) R (cHadReg rMeas)
  have hSuppH := supportedOn_cHadReg_mul rMeas hInvM hSupp
  have s2 := subspaceStep_dPhaseKickHole218Aux hm v rCore rMeas rScr hCS hMS 18 le_rfl hSuppH
  have s3 := subspaceStep_of_circuit (Var := Var)
    ((uKickPrefix218 18 le_rfl rCore rMeas).1 * ((cHadReg rMeas).eval.1 * R)) (cHadReg rMeas)
  refine subspaceStep_congr_out (s1.seq (s2.seq s3)) ?_
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Submonoid.coe_mul, ← Submonoid.coe_mul,
      cHadReg_meas_conj_uKickPrefix218_eq_uLensLoad rData selCore rMeas hDM]
theorem rElecSlot_inj {n : ℕ} (rCore : QRegister posCoreWires n)
    {e₁ e₂ : Fin 218} {j₁ j₂ : Fin 18}
    (h : rElecSlot rCore e₁ j₁ = rElecSlot rCore e₂ j₂) : e₁ = e₂ ∧ j₁ = j₂ := by
  simp only [rElecSlot, QRegister.slice_apply] at h
  have hv := congrArg Fin.val (rCore.wires.injective h)
  dsimp only at hv
  have := j₁.isLt; have := j₂.isLt
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
/-- `0-T` CNOT fan-in on a single slot `e : Fin 218`, XORing `{j | f j = true ∧ j ≠ j₀}` into
  `j₀`. -/
def cSingleSlotFanInAux {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18)
    (rCore : QRegister posCoreWires n) (e : Fin 218) : ∀ (k : ℕ), k ≤ 18 → Circuit n
  | 0, _ => .identity
  | k + 1, hk =>
      if h : f ⟨k, hk⟩ = true ∧ (⟨k, hk⟩ : Fin 18) ≠ j₀ then
        cSingleSlotFanInAux f j₀ rCore e k (by omega) ;;ᶜ
        Circuit.CNOT (rElecSlot rCore e ⟨k, hk⟩) (rElecSlot rCore e j₀)
          (fun heq ↦ h.2 (rElecSlot_inj rCore heq).2)
      else
        cSingleSlotFanInAux f j₀ rCore e k (by omega)
theorem cSingleSlotFanInAux_count {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18)
    (rCore : QRegister posCoreWires n) (e : Fin 218) :
    ∀ (k : ℕ) (hk : k ≤ 18),
      (cSingleSlotFanInAux f j₀ rCore e k hk).count TOFF = 0 ∧
      (cSingleSlotFanInAux f j₀ rCore e k hk).count T = 0
  | 0, _ => ⟨rfl, rfl⟩
  | k + 1, hk => by
      dsimp only [cSingleSlotFanInAux]
      obtain ⟨h1, h2⟩ := cSingleSlotFanInAux_count f j₀ rCore e k (by omega)
      split_ifs <;> simp [Circuit.count, h1, h2]
theorem cSingleSlotFanInAux_eval_ket {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18)
    (rCore : QRegister posCoreWires n) (e : Fin 218) (β : BitAssignment n) :
    ∀ (k : ℕ) (hk : k ≤ 18),
      (cSingleSlotFanInAux f j₀ rCore e k hk).eval.1.mulVec (ket β) =
        ket (Function.update β (rElecSlot rCore e j₀)
          (β (rElecSlot rCore e j₀) +
            ∑ j : Fin k, if f ⟨j.val, by omega⟩ = true ∧ (⟨j.val, by omega⟩ : Fin 18) ≠ j₀ then
              β (rElecSlot rCore e ⟨j.val, by omega⟩) else 0))
  | 0, _ => by simp [cSingleSlotFanInAux, Matrix.one_mulVec]
  | k + 1, hk => by
      dsimp only [cSingleSlotFanInAux]
      have ih := cSingleSlotFanInAux_eval_ket f j₀ rCore e β k (by omega)
      by_cases hc : f ⟨k, hk⟩ = true ∧ (⟨k, hk⟩ : Fin 18) ≠ j₀
      · rw [dite_eq_left hc, eval_seq_mulVec, ih, ket_CNOT]
        refine congrArg ket (funext fun w ↦ ?_)
        have hne : rElecSlot rCore e ⟨k, hk⟩ ≠ rElecSlot rCore e j₀ :=
          fun heq ↦ hc.2 (rElecSlot_inj rCore heq).2
        by_cases hw : w = rElecSlot rCore e j₀
        · subst hw
          rw [Function.update_self, Function.update_self, Function.update_of_ne hne,
              Function.update_self, Fin.sum_univ_castSucc]
          dsimp only [Fin.val_castSucc, Fin.val_last]
          rw [ite_eq_left hc, add_assoc]
        · rw [Function.update_of_ne hw, Function.update_of_ne hw, Function.update_of_ne hw]
      · rw [dite_eq_right hc, ih]
        refine congrArg (fun s ↦ ket (Function.update β (rElecSlot rCore e j₀)
          (β (rElecSlot rCore e j₀) + s))) ?_
        rw [Fin.sum_univ_castSucc]
        dsimp only [Fin.val_castSucc, Fin.val_last]
        rw [ite_eq_right hc, add_zero]
/-- `0-T` CNOT fan-in across the first `m ≤ 218` slots of `rCore`. -/
def cSlotParityFanInAux {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18)
    (rCore : QRegister posCoreWires n) : ∀ (m : ℕ), m ≤ 218 → Circuit n
  | 0, _ => .identity
  | m + 1, hm =>
      cSlotParityFanInAux f j₀ rCore m (by omega) ;;ᶜ
      cSingleSlotFanInAux f j₀ rCore ⟨m, hm⟩ 18 le_rfl
def cSlotParityFanIn {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18)
    (rCore : QRegister posCoreWires n) : Circuit n :=
  cSlotParityFanInAux f j₀ rCore 218 le_rfl
theorem cSlotParityFanInAux_count {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18)
    (rCore : QRegister posCoreWires n) :
    ∀ (m : ℕ) (hm : m ≤ 218),
      (cSlotParityFanInAux f j₀ rCore m hm).count TOFF = 0 ∧
      (cSlotParityFanInAux f j₀ rCore m hm).count T = 0
  | 0, _ => ⟨rfl, rfl⟩
  | m + 1, hm => by
      dsimp only [cSlotParityFanInAux]
      obtain ⟨h1, h2⟩ := cSlotParityFanInAux_count f j₀ rCore m (by omega)
      obtain ⟨h3, h4⟩ := cSingleSlotFanInAux_count f j₀ rCore ⟨m, hm⟩ 18 le_rfl
      simp [Circuit.count, h1, h2, h3, h4]
/-- Bit assignment after `0-T` CNOT fan-in across the first `m ≤ 218` slots of `rCore`. -/
def fanInBits {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18)
    (rCore : QRegister posCoreWires n) : ∀ (m : ℕ), m ≤ 218 → BitAssignment n → BitAssignment n
  | 0, _, β => β
  | m + 1, hm, β =>
      Function.update (fanInBits f j₀ rCore m (by omega) β) (rElecSlot rCore ⟨m, hm⟩ j₀)
        (β (rElecSlot rCore ⟨m, hm⟩ j₀) +
          ∑ j : Fin 18, if f j = true ∧ j ≠ j₀ then β (rElecSlot rCore ⟨m, hm⟩ j) else 0)
theorem fanInBits_apply_other {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18)
    (rCore : QRegister posCoreWires n) (β : BitAssignment n) :
    ∀ (m : ℕ) (hm : m ≤ 218) (w : Wire n),
      (∀ e : Fin m, w ≠ rElecSlot rCore ⟨e.val, by omega⟩ j₀) →
      fanInBits f j₀ rCore m hm β w = β w
  | 0, _, _, _ => rfl
  | m + 1, hm, w, hw => by
      dsimp only [fanInBits]
      rw [Function.update_of_ne (hw ⟨m, Nat.lt_succ_self m⟩)]
      exact fanInBits_apply_other f j₀ rCore β m (by omega) w
        (fun e ↦ hw ⟨e.val, by omega⟩)
theorem fanInBits_apply_slot {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18)
    (rCore : QRegister posCoreWires n) (β : BitAssignment n) :
    ∀ (m : ℕ) (hm : m ≤ 218) (e : Fin m),
      fanInBits f j₀ rCore m hm β (rElecSlot rCore ⟨e.val, by omega⟩ j₀) =
        β (rElecSlot rCore ⟨e.val, by omega⟩ j₀) +
          ∑ j : Fin 18, if f j = true ∧ j ≠ j₀ then
            β (rElecSlot rCore ⟨e.val, by omega⟩ j) else 0
  | 0, _, e => Fin.elim0 e
  | m + 1, hm, e => by
      dsimp only [fanInBits]
      by_cases hem : e.val = m
      · have hSlot : (⟨e.val, by omega⟩ : Fin 218) = ⟨m, hm⟩ := Fin.ext hem
        simp only [hSlot, Function.update_self]
      · have hne : rElecSlot rCore ⟨e.val, by omega⟩ j₀ ≠ rElecSlot rCore ⟨m, hm⟩ j₀ :=
          fun heq ↦ hem (congrArg Fin.val (rElecSlot_inj rCore heq).1)
        rw [Function.update_of_ne hne]
        exact fanInBits_apply_slot f j₀ rCore β m (by omega) ⟨e.val, by omega⟩
theorem cSlotParityFanInAux_eval_ket {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18)
    (rCore : QRegister posCoreWires n) (β : BitAssignment n) : ∀ (m : ℕ) (hm : m ≤ 218),
    (cSlotParityFanInAux f j₀ rCore m hm).eval.1.mulVec (ket β) = ket
    (fanInBits f j₀ rCore m hm β) := by
  intro m
  induction m with
  | zero =>
      intro hm
      change (1 : Unitary (2 ^ n)).1.mulVec (ket β) = ket β
      rw [OneMemClass.coe_one, Matrix.one_mulVec]
  | succ m ih =>
      intro hm
      dsimp only [cSlotParityFanInAux, fanInBits]
      rw [eval_seq_mulVec, ih (by omega),
          cSingleSlotFanInAux_eval_ket f j₀ rCore ⟨m, hm⟩ _ 18 le_rfl]
      have hPrevNotM : ∀ j : Fin 18,
          fanInBits f j₀ rCore m (by omega) β (rElecSlot rCore ⟨m, hm⟩ j) =
            β (rElecSlot rCore ⟨m, hm⟩ j) := fun j ↦
        fanInBits_apply_other f j₀ rCore β m (by omega) _ fun e heq ↦ by
          have hv := congrArg Fin.val (rElecSlot_inj rCore heq).1
          dsimp at hv; omega
      refine congrArg (fun v ↦ ket (Function.update (fanInBits f j₀ rCore m (by omega) β)
        (rElecSlot rCore ⟨m, hm⟩ j₀) v)) ?_
      rw [hPrevNotM j₀]
      refine congrArg (fun s ↦ β (rElecSlot rCore ⟨m, hm⟩ j₀) + s) ?_
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rcases j with ⟨jv, hjv⟩
      dsimp only
      by_cases hj : f ⟨jv, hjv⟩ = true ∧ (⟨jv, hjv⟩ : Fin 18) ≠ j₀
      · rw [ite_eq_left hj, ite_eq_left hj, hPrevNotM ⟨jv, hjv⟩]
      · rw [ite_eq_right hj, ite_eq_right hj]
theorem fanInBits_involutive {n : ℕ} (f : Fin 18 → Bool) (j₀ : Fin 18)
    (rCore : QRegister posCoreWires n) (β : BitAssignment n) :
    fanInBits f j₀ rCore 218 le_rfl (fanInBits f j₀ rCore 218 le_rfl β) = β := by
  funext w
  by_cases hex : ∃ e : Fin 218, w = rElecSlot rCore e j₀
  · obtain ⟨e, rfl⟩ := hex
    have hSlot := fanInBits_apply_slot f j₀ rCore (fanInBits f j₀ rCore 218 le_rfl β) 218 le_rfl e
    have hSlotβ := fanInBits_apply_slot f j₀ rCore β 218 le_rfl e
    have heEq : (⟨e.val, by omega⟩ : Fin 218) = e := Fin.ext rfl
    simp only [heEq] at hSlot hSlotβ
    rw [hSlot, hSlotβ]
    have hSame : (∑ j : Fin 18, if f j = true ∧ j ≠ j₀ then
          fanInBits f j₀ rCore 218 le_rfl β (rElecSlot rCore e j) else 0) =
        ∑ j : Fin 18, if f j = true ∧ j ≠ j₀ then β (rElecSlot rCore e j) else 0 := by
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      by_cases hj : f j = true ∧ j ≠ j₀
      · rw [ite_eq_left hj, ite_eq_left hj,
            fanInBits_apply_other f j₀ rCore β 218 le_rfl _
              (fun e' heq ↦ hj.2 (rElecSlot_inj rCore heq).2)]
      · rw [ite_eq_right hj, ite_eq_right hj]
    rw [hSame, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  · rw [fanInBits_apply_other f j₀ rCore _ 218 le_rfl w (fun e heq ↦ hex ⟨e, heq⟩),
        fanInBits_apply_other f j₀ rCore β 218 le_rfl w (fun e heq ↦ hex ⟨e, heq⟩)]
/-- 4 zero-T `CZ` gates between `uHi[0..4)` (`rScr[64..68)`) and `rRow70[0..4)` (`rScr[70..74)`). -/
def cCz4RowHi {n mScr : ℕ} (hm : 75 ≤ mScr) (rScr : QRegister mScr n) : Circuit n :=
  let uHi : Fin 4 → Wire n := fun h ↦ rScr ⟨64 + h.val, by omega⟩
  let rRow4 : QRegister 4 n := p2dSubReg rScr 70 4 (by omega)
  have hne : ∀ h : Fin 4, uHi h ≠ rRow4 h := fun h heq ↦ by
    have hr : rRow4 h = rScr ⟨70 + h.val, by omega⟩ :=
      congrArg rScr.wires (Fin.ext (by dsimp [rRow4, p2dSubReg]))
    exact rSub_ne_of_ne rScr (by omega) (by omega) (by omega) (heq.trans hr)
  czCircuit (uHi 0) (rRow4 0) (hne 0) ;;ᶜ
    (czCircuit (uHi 1) (rRow4 1) (hne 1) ;;ᶜ
      (czCircuit (uHi 2) (rRow4 2) (hne 2) ;;ᶜ czCircuit (uHi 3) (rRow4 3) (hne 3)))
theorem cCz4RowHi_count {n mScr : ℕ} (hm : 75 ≤ mScr) (rScr : QRegister mScr n) :
    (cCz4RowHi hm rScr).count TOFF = 0 ∧ (cCz4RowHi hm rScr).count T = 0 := by
  dsimp only [cCz4RowHi]
  simp [Circuit.count_seq, czCircuit_count_toff, czCircuit_count_t]
theorem cCz4RowHi_eval_ket {n mScr : ℕ} (hm : 75 ≤ mScr) (rScr : QRegister mScr n)
    (α : BitAssignment n) (h₀ : ℕ) (hh₀ : h₀ < 4)
    (hHi : ∀ h : Fin 4, α (rScr ⟨64 + h.val, by omega⟩) = if h.val = h₀ then 1 else 0) :
    (cCz4RowHi hm rScr).eval.1.mulVec (ket α) =
      ((-1 : ℂ) ^ (α (p2dSubReg rScr 70 4 (by omega) ⟨h₀, hh₀⟩)).val) • ket α := by
  dsimp only [cCz4RowHi]
  rw[eval_seq_mulVec, ket_czCircuit, Matrix.mulVec_smul, eval_seq_mulVec, ket_czCircuit,
      Matrix.mulVec_smul, eval_seq_mulVec, ket_czCircuit, Matrix.mulVec_smul, ket_czCircuit,
      smul_smul, smul_smul, smul_smul]
  refine congrArg (· • ket α) ?_
  have h0 := hHi 0; have h1 := hHi 1; have h2 := hHi 2; have h3 := hHi 3
  rw [h0, h1, h2, h3]
  rcases (by omega : h₀ = 0 ∨ h₀ = 1 ∨ h₀ = 2 ∨ h₀ = 3) with rfl | rfl | rfl | rfl
  · have hf : (⟨0, hh₀⟩ : Fin 4) = 0 := rfl; rw [hf]; simp
  · have hf : (⟨1, hh₀⟩ : Fin 4) = 1 := rfl; rw [hf]; simp
  · have hf : (⟨2, hh₀⟩ : Fin 4) = 2 := rfl; rw [hf]; simp
  · have hf : (⟨3, hh₀⟩ : Fin 4) = 3 := rfl; rw [hf]; simp
noncomputable def uZKick1BitShifted218 {n : ℕ} (j₀ : Fin 18)
    (rCore : QRegister posCoreWires n) : Unitary (2 ^ n) :=
  diagSignUnitary fun g ↦
    let β := basisBits n g
    let s₀ := shiftedPartnerSlotFast (fun w ↦ β (rCore w))
    decide (β (rElecSlot rCore s₀ j₀) = 1)
noncomputable def dZKick1BitHole218 {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr) (v : Var)
    (j₀ : Fin 18) (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) : DynamicCircuit Var n :=
  let rRow70 := p2dSubReg rScr 70 4 (by omega)
  let hBuf := rowBufDisj_scr70 hm rCore rScr hCS
  .seq (.circuit (cLoad4Rows218Into hm j₀ rCore rScr rRow70 hCS hBuf ;;ᶜ cCz4RowHi hm rScr))
    (dUncompute4Rows218 hm v j₀ rCore rScr rRow70 hCS)
theorem dZKick1BitHole218_count {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr)
    (v : Var) (j₀ : Fin 18)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) :
    (dZKick1BitHole218 (Var := Var) hm v j₀ rCore rScr hCS).count TOFF = 0 ∧
    (dZKick1BitHole218 (Var := Var) hm v j₀ rCore rScr hCS).count T = 436 := by
  dsimp only [dZKick1BitHole218, DynamicCircuit.count]
  obtain ⟨hCzToff, hCzT⟩ := cCz4RowHi_count hm rScr
  rw [Circuit.count_seq, Circuit.count_seq, cLoad4Rows218Into_count_toff, hCzToff,
      cLoad4Rows218Into_count_t, hCzT, dUncompute4Rows218_count_toff, dUncompute4Rows218_count_t]
  exact ⟨rfl, rfl⟩
theorem subspaceStep_dZKick1BitHole218 {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mScr : ℕ} [NeZero (2 ^ n)] (hm : 75 ≤ mScr) (v : Var) (j₀ : Fin 18)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) {R : Operator (2 ^ n)}
    (hSupp : SupportedOn (InvHoleShifted218 hm rCore rScr) R) : SubspaceStep R
    ((uZKick1BitShifted218 j₀ rCore).1 * R) (dZKick1BitHole218 hm v j₀ rCore rScr hCS) := by
  let rRow70 := p2dSubReg rScr 70 4 (by omega)
  let hBuf := rowBufDisj_scr70 hm rCore rScr hCS
  let cPre := cLoad4Rows218Into hm j₀ rCore rScr rRow70 hCS hBuf ;;ᶜ cCz4RowHi hm rScr
  have hSuppBase : SupportedOn (fun β ↦ (∀ r : Fin 4, β (rRow70 r) = 0) ∧
      InvHoleBase218 hm rCore rScr β) R :=
    supportedOn_mono (fun β h ↦ (invHoleShifted218_iff_base hm rCore rScr β).mp h) hSupp
  have s1 : SubspaceStep (Var := Var) R
      ((uHold1Bit rCore rRow70 j₀ hBuf.1).1 * ((uZKick1BitShifted218 j₀ rCore).1 * R))
      (.circuit cPre) := by
    refine subspaceStep_congr_out (subspaceStep_of_circuit R cPre) ?_
    rw [← Matrix.mul_assoc]
    refine hSuppBase _ _ fun β ⟨hRow0, hLo, hHi, hPar0, _⟩ ↦ ?_
    let s₀ := shiftedPartnerSlotFast (fun w ↦ β (rCore w))
    have hh₀ : s₀.val / 64 < 4 := by have := s₀.isLt; omega
    have hl₀ : s₀.val % 64 < 64 := Nat.mod_lt _ (by decide)
    let vals := rowBit218 rCore j₀ β (s₀.val % 64)
    let α₁ := p2d_writeReg β rRow70 vals
    have hα₁_hi : ∀ h : Fin 4, α₁ (rScr ⟨64 + h.val, by omega⟩) = if h.val = s₀.val / 64 then 1
        else 0 :=
      fun h ↦ (p2d_writeReg_apply_of_not_mem _ _ _ _ fun ⟨r, hr⟩ ↦
        (hBuf.2 ⟨64 + h.val, by omega⟩ r (Or.inl (by dsimp; omega))) hr.symm).trans (hHi h)
    rw [eval_seq_mulVec,
        cLoad4Rows218Into_eval_ket hm j₀ rCore rScr rRow70 hCS hBuf β hRow0 hPar0 (s₀.val % 64) hl₀
            hLo,
        cCz4RowHi_eval_ket hm rScr α₁ (s₀.val / 64) hh₀ hα₁_hi]
    change ((-1 : ℂ) ^ (p2d_writeReg β rRow70 vals (rRow70 ⟨s₀.val / 64, hh₀⟩)).val) • ket α₁ = _
    rw [p2d_writeReg_apply_reg β rRow70 vals ⟨s₀.val / 64, hh₀⟩]
    dsimp only [vals]
    rw [rowBit218_at_active rCore j₀ β s₀,
        ← Matrix.mulVec_mulVec, uZKick1BitShifted218, diagSignUnitary_mulVec_ket,
        Matrix.mulVec_smul, uHold1Bit_mulVec_ket, hold1BitMap_eq_writeReg_of_zero rCore rRow70 j₀
            hRow0]
    have hβ : basisBits n ((basisBitsEquiv n).symm β) = β := (basisBitsEquiv n).apply_symm_apply β
    simp only [hβ, ite_decide_eq_one_zmod2]
    rfl
  have hSuppZ : SupportedOn (fun β ↦ (∀ r : Fin 4, β (rRow70 r) = 0) ∧
      InvHoleBase218 hm rCore rScr β) ((uZKick1BitShifted218 j₀ rCore).1 * R) :=
    supportedOn_diagSignUnitary_mul _ hSuppBase
  have s2 := subspaceStep_dUncompute4Rows218 hm v j₀ rCore rScr rRow70 hCS hBuf.1 hSuppZ
  exact s1.seq s2
/-- Classical-branch phase-fix dynamic circuit at `.hole` (`≤ 436 T`, `TOFF = 0`) for outcome `f :
  Fin 18 → Bool`. -/
noncomputable def dFixHole218 {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr) (v : Var)
    (f : Fin 18 → Bool) (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) : DynamicCircuit Var n :=
  match findTrueBitAux f 18 le_rfl with
  | none => .circuit .identity
  | some j₀ =>
      let cFan := cSlotParityFanIn f j₀ rCore
      .seq (.circuit cFan)
        (.seq (dZKick1BitHole218 hm v j₀ rCore rScr hCS) (.circuit cFan))
theorem dFixHole218_count_toff {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr)
    (v : Var) (f : Fin 18 → Bool)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) :
    (dFixHole218 (Var := Var) hm v f rCore rScr hCS).count TOFF = 0 := by
  dsimp only [dFixHole218]
  cases findTrueBitAux f 18 le_rfl with
  | none => rfl
  | some j₀ =>
      obtain ⟨hFanToff, _⟩ := cSlotParityFanInAux_count f j₀ rCore 218 le_rfl
      obtain ⟨hZToff, _⟩ := dZKick1BitHole218_count (Var := Var) hm v j₀ rCore rScr hCS
      simp [DynamicCircuit.count, cSlotParityFanIn, hFanToff, hZToff]
theorem dFixHole218_count_t_le {Var : Type} {n mScr : ℕ} (hm : 75 ≤ mScr)
    (v : Var) (f : Fin 18 → Bool)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) :
    (dFixHole218 (Var := Var) hm v f rCore rScr hCS).count T ≤ 436 := by
  dsimp only [dFixHole218]
  cases findTrueBitAux f 18 le_rfl with
  | none => exact Nat.zero_le 436
  | some j₀ =>
      obtain ⟨_, hFanT⟩ := cSlotParityFanInAux_count f j₀ rCore 218 le_rfl
      obtain ⟨_, hZT⟩ := dZKick1BitHole218_count (Var := Var) hm v j₀ rCore rScr hCS
      simp [DynamicCircuit.count, cSlotParityFanIn, hFanT, hZT]
theorem subspaceStep_dFixHole218 {Var : Type} [Fintype Var] [DecidableEq Var]
    {n kData mScr : ℕ} [NeZero (2 ^ n)] (hm : 75 ≤ mScr) (v : Var) (f : Fin 18 → Bool)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rScr : QRegister mScr n) (hCS : (rData.compose selCore).DisjointWires rScr)
    {R : Operator (2 ^ n)} (hSupp : SupportedOn (InvHoleShifted218 hm (rData.compose selCore)
    rScr) R) : SubspaceStep R ((rData.embedUnitary (diagSignUnitary (fun d ↦ f2Parity 18 f
    ((shiftedPartnerLens218 selCore).tbl d)))).1 * R)
    (dFixHole218 hm v f (rData.compose selCore) rScr hCS) := by
  let rCore := rData.compose selCore
  dsimp only [dFixHole218]
  obtain ⟨hSome, hNone⟩ := findTrueBitAux_spec f 18 le_rfl
  cases hfind : findTrueBitAux f 18 le_rfl with
  | none =>
      have hfFalse : ∀ j : Fin 18, f j = false := fun j ↦ hNone hfind j.val j.isLt
      have hParFalse : (fun d : Fin (2 ^ kData) ↦ f2Parity 18 f ((shiftedPartnerLens218
          selCore).tbl d)) =
          fun _ ↦ false := by
        funext d
        have hprod := sign_f2Parity_eq_prod 18 f ((shiftedPartnerLens218 selCore).tbl d)
        simp only [hfFalse, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Finset.prod_const_one]
            at hprod
        cases hfp : f2Parity 18 f ((shiftedPartnerLens218 selCore).tbl d)
        · rfl
        · rw [hfp] at hprod; norm_num at hprod
      rw [hParFalse, diagSignUnitary_false, rData.embedUnitary_one]
      exact subspaceStep_congr_out (subspaceStep_of_circuit (Var := Var) R .identity) (by simp)
  | some j₀ =>
      have hf0 : f j₀ = true := hSome j₀ hfind
      let cFan := cSlotParityFanIn f j₀ rCore
      let UZ := uZKick1BitShifted218 j₀ rCore
      have hFanOther : ∀ (β : BitAssignment n) (w : Wire n),
          (∀ e : Fin 218, w ≠ rElecSlot rCore e j₀) →
          fanInBits f j₀ rCore 218 le_rfl β w = β w := fun β w hw ↦
        fanInBits_apply_other f j₀ rCore β 218 le_rfl w fun e ↦ hw ⟨e.val, by omega⟩
      have hSlotFan : ∀ β : BitAssignment n,
          shiftedPartnerSlotFast (fun w ↦ fanInBits f j₀ rCore 218 le_rfl β (rCore w)) =
            shiftedPartnerSlotFast (fun w ↦ β (rCore w)) := fun β ↦
        shiftedPartnerSlotFast_congr_outside fun w hwLo _ ↦
          hFanOther β (rCore w) fun e heq ↦ by
            have h1 : rElecSlot rCore e j₀ = rCore (rElecSlot (QRegExt.ofFin posCoreWires) e j₀)
                := rfl
            rw [h1] at heq
            have hv := congrArg Fin.val (rCore.wires.injective heq)
            rw [rElecSlot_ofFin_val_local] at hv
            have := e.isLt; have := j₀.isLt; omega
      have hSuppFan : SupportedOn (InvHoleShifted218 hm rCore rScr) (cFan.eval.1 * R) := by
        refine supportedOn_unitary_mul cFan.eval.1 (fanInBits f j₀ rCore 218 le_rfl)
          (fun β ↦ cSlotParityFanInAux_eval_ket f j₀ rCore β 218 le_rfl)
          (fun β hInv ↦ ?_) hSupp
        have hS : ∀ k : Fin mScr, fanInBits f j₀ rCore 218 le_rfl β (rScr k) = β (rScr k) :=
          fun k ↦ hFanOther β _ fun e ↦ (rCore_ne_rSub hCS _ _ _).symm
        have hSub : ∀ r : Fin 4, fanInBits f j₀ rCore 218 le_rfl β
            (p2dSubReg rScr 70 4 (by omega) r) = β (p2dSubReg rScr 70 4 (by omega) r) :=
          fun r ↦ hS ⟨70 + r.val, by omega⟩
        dsimp only [InvHoleShifted218] at hInv ⊢
        simp only [hSlotFan β, hS, hSub]
        exact hInv
      have s1 := subspaceStep_of_circuit (Var := Var) R cFan
      have s2 := subspaceStep_dZKick1BitHole218 hm v j₀ rCore rScr hCS hSuppFan
      have s3 := subspaceStep_of_circuit (Var := Var) (UZ.1 * (cFan.eval.1 * R)) cFan
      refine subspaceStep_congr_out (s1.seq (s2.seq s3)) ?_
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Submonoid.coe_mul, ← Submonoid.coe_mul]
      refine congrArg (fun U : Unitary (2 ^ n) ↦ U.1 * R) ?_
      apply Subtype.ext; apply matrix_ext_ket; intro β
      rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      let β' := fanInBits f j₀ rCore 218 le_rfl β
      have hKet1 : cFan.eval.1.mulVec (ket β) = ket β' :=
        cSlotParityFanInAux_eval_ket f j₀ rCore β 218 le_rfl
      have hKet2 : cFan.eval.1.mulVec (ket β') = ket β := by
        dsimp only [cFan, cSlotParityFanIn]
        rw [cSlotParityFanInAux_eval_ket f j₀ rCore β' 218 le_rfl,
            fanInBits_involutive f j₀ rCore β]
      dsimp only [UZ, uZKick1BitShifted218]
      rw [hKet1, diagSignUnitary_mulVec_ket, Matrix.mulVec_smul, hKet2,
          embedUnitary_diagSignUnitary, diagSignUnitary_mulVec_ket]
      have hβ'Eq : basisBits n ((basisBitsEquiv n).symm β') = β' :=
        (basisBitsEquiv n).apply_symm_apply β'
      let g := (basisBitsEquiv n).symm β
      have hgβ : basisBits n g = β := (basisBitsEquiv n).apply_symm_apply β
      simp only [hβ'Eq, ite_decide_eq_one_zmod2]
      refine congrArg (· • ket β) ?_
      let eAct : Fin 218 := shiftedPartnerSlotFast (fun w ↦ β (rCore w))
      have hValβ' : β' (rElecSlot rCore eAct j₀) =
          ∑ j : Fin 18, if f j = true then β (rElecSlot rCore eAct j) else 0 := by
        dsimp only [β']
        have hSlot := fanInBits_apply_slot f j₀ rCore β 218 le_rfl eAct
        have heEq : (⟨eAct.val, by omega⟩ : Fin 218) = eAct := Fin.ext rfl
        simp only [heEq] at hSlot
        rw [hSlot]
        have hSingle : β (rElecSlot rCore eAct j₀) =
            ∑ j : Fin 18, if j = j₀ then (if f j = true then β (rElecSlot rCore eAct j) else 0)
                else 0 := by
          rw [Finset.sum_ite_eq' Finset.univ j₀]
          simp [hf0]
        rw [hSingle, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        by_cases hj : j = j₀
        · subst hj; simp [hf0]
        · simp [hj]
      rw [hSlotFan β, hValβ', neg_one_pow_sum_zmod2, sign_f2Parity_eq_prod]
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      have hTblBit : basisBits 18 ((shiftedPartnerLens218 selCore).tbl (rData.extractIndex g)) j =
          β (rElecSlot rCore eAct j) := by
        rw [basisBits_shiftedPartnerLens218_tbl_eq rData selCore g j, hgβ]
      rw [← hTblBit]
      exact sign_zmod2_bool_if (f j) (basisBits 18 ((shiftedPartnerLens218 selCore).tbl
          (rData.extractIndex g)) j)
attribute [irreducible]
  toDynWGLocal cHadRegAux cHadReg cLoad4Rows218Into cFixSingleRow218 cBranchFix4Rows218Aux
  dSelectKickFrom4Rows dUncompute4Rows218 dKick1Bit218 dPhaseKickHole218Aux dPhaseKickHole218
  dLoadHole218 cSingleSlotFanInAux cSlotParityFanInAux cSlotParityFanIn cCz4RowHi
  dZKick1BitHole218 dFixHole218
end BoothOpt_P4_10_TwoLoadHeldRowTrueSwap
end
end BoothOpt_P4_10a_TwoLoadHeldRowCore

noncomputable section SlimStageADepsC

section
set_option maxRecDepth 131072
set_option exponentiation.threshold 256
section SharedScope
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
local instance (priority := 1000000) instNeZeroSub (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix _root_.DynamicCircuit DynCircuitExt Real
open Circuit hiding TOFF
open PrimitiveGate (T TOFF)
open scoped Matrix BigOperators
open StageADeconstrCore (selDataInAct selMeasInAct)
namespace ForestQft117BundleNoTopBridge
section ConfigK7
set_option maxRecDepth 131072
open HermitianMat
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open KaratsubaQft64Matrix (omega128 omega128_add star_mul_omega128_self bitXor bit6 bitRev6)
open DyadicQft64Engine DyadicQft64 DyadicQft64WalkCircuit DyadicQft64WalkCircuit288
open FullSysCatSegmentBridge (FullSysQft654Bundle fullSysCoreWires)
open NuclearTwistRealizes (slot2AxisSum)
open CoreQftHadamard140And160 (CanonStageSpec128 nCanon4062 rQftCanon128 rWorkCanon128 rSysCanon128
  rPGCanon128 rSysCanon128_disjoint_rPGCanon128 rSysCanon128_disjoint_rWorkCanon128
  rPGCanon128_disjoint_rWorkCanon128 concat_compose_rQftCanon128 concat_compose_rWorkCanon128
  toFullSysQft654BundleOfLe128)
open HeadMod4Wide178 (pointAxisPhaseExp128 omega128_eq_of_emod_eq)
open StageAPosHeadConjugatedCircuit (uCoreHadamard6)
open TwistStreamEliminationAux (spectatorSum217)
open HeldRSum42TwistQftPass2Stitch (rAxisPrefix rAxisPrefix_disjoint
  axisProdPrefix CanonStageSpec128.ofAxisPrefixCircuit stageHPrefixCanonStage128)
noncomputable def dCanonStage128Fwd {Var : Type} {n mWork : ℕ} (S : CanonStageSpec128)
    (hm : 128 ≤ mWork) (v : Var) (rCat : QRegister (3924 + 3 + 7) n)
    (rWork : QRegister mWork n) (hCW : rCat.DisjointWires rWork) : DynamicCircuit Var n :=
  let hw0 : 0 + 128 ≤ mWork := Nat.zero_add 128 ▸ hm
  let rW128 := rWork.slice 0 128 hw0
  let hDisj : rCat.DisjointWires rW128 := hCW.compose_right (QRegister.block 0 128 hw0)
  liftDynamic v (rCat.concat rW128 hDisj) S.dFwd
/-- Inverse dynamic circuit lifting any `S : CanonStageSpec128` to `(rCat, rWork)` (`128 ≤
  mWork`). -/
noncomputable def dCanonStage128Inv {Var : Type} {n mWork : ℕ} (S : CanonStageSpec128)
    (hm : 128 ≤ mWork) (v : Var) (rCat : QRegister (3924 + 3 + 7) n)
    (rWork : QRegister mWork n) (hCW : rCat.DisjointWires rWork) : DynamicCircuit Var n :=
  let hw0 : 0 + 128 ≤ mWork := Nat.zero_add 128 ▸ hm
  let rW128 := rWork.slice 0 128 hw0
  let hDisj : rCat.DisjointWires rW128 := hCW.compose_right (QRegister.block 0 128 hw0)
  liftDynamic v (rCat.concat rW128 hDisj) S.dInv
@[simp] theorem count_dCanonStage128Fwd_toff {Var : Type} {n mWork : ℕ}
    (S : CanonStageSpec128) (hm : 128 ≤ mWork) (v : Var) (rCat : QRegister (3924 + 3 + 7) n)
    (rWork : QRegister mWork n) (hCW : rCat.DisjointWires rWork) :
    (dCanonStage128Fwd S hm v rCat rWork hCW).count TOFF = 0 :=
    (count_liftDynamic TOFF v _ S.dFwd).trans S.hToffFwd
@[simp] theorem count_dCanonStage128Inv_toff {Var : Type} {n mWork : ℕ}
    (S : CanonStageSpec128) (hm : 128 ≤ mWork) (v : Var) (rCat : QRegister (3924 + 3 + 7) n)
    (rWork : QRegister mWork n) (hCW : rCat.DisjointWires rWork) :
    (dCanonStage128Inv S hm v rCat rWork hCW).count TOFF = 0 :=
    (count_liftDynamic TOFF v _ S.dInv).trans S.hToffInv
@[simp] theorem count_dCanonStage128Fwd_t {Var : Type} {n mWork : ℕ} (S : CanonStageSpec128)
    (hm : 128 ≤ mWork) (v : Var) (rCat : QRegister (3924 + 3 + 7) n)
    (rWork : QRegister mWork n) (hCW : rCat.DisjointWires rWork) :
    (dCanonStage128Fwd S hm v rCat rWork hCW).count .T = S.tCost :=
    (count_liftDynamic .T v _ S.dFwd).trans S.hTFwd
@[simp] theorem count_dCanonStage128Inv_t {Var : Type} {n mWork : ℕ} (S : CanonStageSpec128)
    (hm : 128 ≤ mWork) (v : Var) (rCat : QRegister (3924 + 3 + 7) n)
    (rWork : QRegister mWork n) (hCW : rCat.DisjointWires rWork) :
    (dCanonStage128Inv S hm v rCat rWork hCW).count .T = S.tCost :=
    (count_liftDynamic .T v _ S.dInv).trans S.hTInv
theorem dCanonStage128Fwd_realizes {Var : Type} [Fintype Var] [DecidableEq Var] {n mWork : ℕ}
    [NeZero (2 ^ n)] (S : CanonStageSpec128) (hm : 128 ≤ mWork) (v : Var)
    (rCat : QRegister (3924 + 3 + 7) n) (rWork : QRegister mWork n)
    (hCW : rCat.DisjointWires rWork) : RealizesEmbeddedUnitaryWithCleanWorkspace rCat rWork
    S.uCat (dCanonStage128Fwd S hm v rCat rWork hCW) := by
  let hw0 : 0 + 128 ≤ mWork := Nat.zero_add 128 ▸ hm
  let rW128 := rWork.slice 0 128 hw0
  let hDisj : rCat.DisjointWires rW128 := hCW.compose_right (QRegister.block 0 128 hw0)
  have hRaw := realizes_liftDynamic v (rCat.concat rW128 hDisj)
    rQftCanon128 rWorkCanon128 S.uCat S.dFwd S.hRealFwd
  rw [concat_compose_rQftCanon128 rCat rW128 hDisj,
    concat_compose_rWorkCanon128 rCat rW128 hDisj] at hRaw
  exact realizes_congr_slice hw0 rfl hRaw
theorem dCanonStage128Inv_realizes {Var : Type} [Fintype Var] [DecidableEq Var] {n mWork : ℕ}
    [NeZero (2 ^ n)] (S : CanonStageSpec128) (hm : 128 ≤ mWork) (v : Var)
    (rCat : QRegister (3924 + 3 + 7) n) (rWork : QRegister mWork n)
    (hCW : rCat.DisjointWires rWork) : RealizesEmbeddedUnitaryWithCleanWorkspace rCat rWork
    S.uCat⁻¹ (dCanonStage128Inv S hm v rCat rWork hCW) := by
  let hw0 : 0 + 128 ≤ mWork := Nat.zero_add 128 ▸ hm
  let rW128 := rWork.slice 0 128 hw0
  let hDisj : rCat.DisjointWires rW128 := hCW.compose_right (QRegister.block 0 128 hw0)
  have hRaw := realizes_liftDynamic v (rCat.concat rW128 hDisj)
    rQftCanon128 rWorkCanon128 S.uCat⁻¹ S.dInv S.hRealInv
  rw [concat_compose_rQftCanon128 rCat rW128 hDisj,
    concat_compose_rWorkCanon128 rCat rW128 hDisj] at hRaw
  exact realizes_congr_slice hw0 rfl hRaw
-- ============================================================================
-- Section 1: Hadamard-Forest `CanonStageSpec128` Engine (`xorForestBatchCanonStage128`) &
-- Active 1-Electron (`117 T` = `234 T/step`) / 2-Electron (`221 T` = `442 T/step`) Forest `QFT_64`
-- ============================================================================
section ApexButterflyEngine128
variable {Var : Type} {n : ℕ}
def cnotPairsCircuit : (wpairs : List (Wire n × Wire n)) → (∀ p ∈ wpairs, p.1 ≠ p.2) → Circuit n
  | [], _ => Circuit.identity
  | p :: rest, hne =>
      Circuit.CNOT p.1 p.2 (hne p List.mem_cons_self) ;;ᶜ
        cnotPairsCircuit rest (fun q hq ↦ hne q (List.mem_cons_of_mem p hq))
@[simp] theorem count_cnotPairsCircuit_toff :
    ∀ (wpairs : List (Wire n × Wire n)) (hne : ∀ p ∈ wpairs, p.1 ≠ p.2),
      (cnotPairsCircuit wpairs hne).count TOFF = 0
  | [], _ => by simp [cnotPairsCircuit]
  | _ :: rest, hne => by simp [cnotPairsCircuit, count_cnotPairsCircuit_toff rest]
@[simp] theorem count_cnotPairsCircuit_t :
    ∀ (wpairs : List (Wire n × Wire n)) (hne : ∀ p ∈ wpairs, p.1 ≠ p.2),
      (cnotPairsCircuit wpairs hne).count .T = 0
  | [], _ => by simp [cnotPairsCircuit]
  | _ :: rest, hne => by simp [cnotPairsCircuit, count_cnotPairsCircuit_t rest]
def cnotPairsPerm : List (Wire n × Wire n) → BitAssignment n → BitAssignment n
  | [], β => β
  | p :: rest, β => cnotPairsPerm rest (Function.update β p.2 (β p.2 + β p.1))
theorem cnotPairsPerm_append :
    ∀ (A B : List (Wire n × Wire n)) (β : BitAssignment n),
      cnotPairsPerm (A ++ B) β = cnotPairsPerm B (cnotPairsPerm A β)
  | [], _, _ => rfl
  | p :: rest, B, β => cnotPairsPerm_append rest B (Function.update β p.2 (β p.2 + β p.1))
theorem cnotPairsPerm_outside :
    ∀ (wpairs : List (Wire n × Wire n)) (β : BitAssignment n) (w : Wire n),
      (∀ p ∈ wpairs, p.2 ≠ w) → cnotPairsPerm wpairs β w = β w
  | [], _, _, _ => rfl
  | p :: rest, β, w, hout => by
      dsimp only [cnotPairsPerm]
      rw [cnotPairsPerm_outside rest _ w (fun q hq ↦ hout q (List.mem_cons_of_mem p hq)),
        Function.update_of_ne (hout p List.mem_cons_self).symm]
theorem cnotPairsPerm_eq_on_superset {S : Finset (Wire n)} :
    ∀ (wpairs : List (Wire n × Wire n)),
      (∀ p ∈ wpairs, p.1 ∈ S ∧ p.2 ∈ S) →
      ∀ {β₁ β₂ : BitAssignment n},
        (∀ w ∈ S, β₁ w = β₂ w) →
        ∀ w ∈ S, cnotPairsPerm wpairs β₁ w = cnotPairsPerm wpairs β₂ w
  | [], _, _, _, hEq, w, hw => hEq w hw
  | p :: rest, hS, β₁, β₂, hEq, w, hw => by
      have hp := hS p List.mem_cons_self
      refine cnotPairsPerm_eq_on_superset rest (fun q hq ↦ hS q (List.mem_cons_of_mem p hq))
        (fun u hu ↦ ?_) w hw
      by_cases hu2 : u = p.2
      · subst hu2
        rw [Function.update_self, Function.update_self, hEq p.2 hp.2, hEq p.1 hp.1]
      · rw [Function.update_of_ne hu2, Function.update_of_ne hu2, hEq u hu]
theorem cnotStep_involutive {c t : Wire n} (hne : c ≠ t) (β : BitAssignment n) :
    let β' := Function.update β t (β t + β c)
    Function.update β' t (β' t + β' c) = β := by
  intro β'
  funext w
  by_cases hw : w = t
  · subst hw
    dsimp only [β']
    rw [Function.update_self, Function.update_self, Function.update_of_ne hne,
      zmod2_add_cancel_right]
  · dsimp only [β']
    rw [Function.update_of_ne hw, Function.update_of_ne hw]
theorem cnotPairsPerm_reverse_cancel :
    ∀ (wpairs : List (Wire n × Wire n)),
      (∀ p ∈ wpairs, p.1 ≠ p.2) →
      ∀ (β : BitAssignment n),
        cnotPairsPerm wpairs.reverse (cnotPairsPerm wpairs β) = β
  | [], _, _ => rfl
  | p :: rest, hne, β => by
      simp only [List.reverse_cons, cnotPairsPerm]
      rw [cnotPairsPerm_append,
        cnotPairsPerm_reverse_cancel rest (fun q hq ↦ hne q (List.mem_cons_of_mem p hq))]
      exact cnotStep_involutive (hne p List.mem_cons_self) β
theorem classicalPerm_cnotPairsCircuit :
    ∀ (wpairs : List (Wire n × Wire n)) (hne : ∀ p ∈ wpairs, p.1 ≠ p.2),
      ClassicalPerm (cnotPairsCircuit wpairs hne) (cnotPairsPerm wpairs)
  | [], _ => ClassicalPerm.identity
  | p :: rest, hne =>
      (ClassicalPerm.CNOT p.1 p.2 (hne p List.mem_cons_self)).seq
        (classicalPerm_cnotPairsCircuit rest (fun q hq ↦ hne q (List.mem_cons_of_mem p hq)))
def localPerm6 : List (Fin 6 × Fin 6) → (Fin 6 → ZMod 2) → (Fin 6 → ZMod 2)
  | [], b => b
  | p :: rest, b => localPerm6 rest (Function.update b p.2 (b p.2 + b p.1))
def axisCnotPairs {kSys : ℕ} (rSys : QRegister kSys n)
    (g : Fin 6 → Fin kSys) (pairs6 : List (Fin 6 × Fin 6)) : List (Wire n × Wire n) :=
  pairs6.map fun p ↦ (rSys (g p.1), rSys (g p.2))
def batchCnotPairs {kSys : ℕ} (rSys : QRegister kSys n) (pairs6 : List (Fin 6 × Fin 6)) :
    ∀ {L : ℕ}, (Fin L → Fin 6 → Fin kSys) → List (Wire n × Wire n)
  | 0, _ => []
  | _ + 1, idxAx =>
      axisCnotPairs rSys (idxAx 0) pairs6 ++
        batchCnotPairs rSys pairs6 (fun l ↦ idxAx l.succ)
theorem batchCnotPairs_hne {kSys : ℕ} (rSys : QRegister kSys n)
    (pairs6 : List (Fin 6 × Fin 6)) (hne6 : ∀ p ∈ pairs6, p.1 ≠ p.2) :
    ∀ {L : ℕ} (idxAx : Fin L → Fin 6 → Fin kSys),
      Function.Injective (fun p : Fin L × Fin 6 ↦ idxAx p.1 p.2) →
      ∀ wp ∈ batchCnotPairs rSys pairs6 idxAx, wp.1 ≠ wp.2
  | 0, _, _, _, hmem => by simp [batchCnotPairs] at hmem
  | _ + 1, idxAx, hinj, wp, hmem => by
      rcases List.mem_append.mp hmem with hhead | htail
      · rcases List.mem_map.mp hhead with ⟨p, hp, rfl⟩
        intro heq
        have hp_eq : ((0, p.1) : Fin _ × Fin 6) = (0, p.2) := hinj (rSys.wires.injective heq)
        exact hne6 p hp (congrArg Prod.snd hp_eq)
      · exact batchCnotPairs_hne rSys pairs6 hne6 (fun l ↦ idxAx l.succ)
          (by
            rintro ⟨a1, a2⟩ ⟨b1, b2⟩ h
            have hab : ((a1.succ, a2) : Fin _ × Fin 6) = (b1.succ, b2) := hinj h
            have h1 : a1.succ = b1.succ := congrArg Prod.fst hab
            have h2 : a2 = b2 := congrArg Prod.snd hab
            exact Prod.ext (Fin.succ_injective _ h1) h2)
          wp htail
theorem batchCnotPairs_mem_sys {kSys : ℕ} (rSys : QRegister kSys n)
    (pairs6 : List (Fin 6 × Fin 6)) :
    ∀ {L : ℕ} (idxAx : Fin L → Fin 6 → Fin kSys)
      (wp : Wire n × Wire n), wp ∈ batchCnotPairs rSys pairs6 idxAx →
      wp.1 ∈ rSys.image ∧ wp.2 ∈ rSys.image
  | 0, _, _, hmem => by simp [batchCnotPairs] at hmem
  | _ + 1, idxAx, wp, hmem => by
      rcases List.mem_append.mp hmem with hhead | htail
      · rcases List.mem_map.mp hhead with ⟨p, _, rfl⟩
        exact ⟨(QRegister.mem_image rSys _).mpr ⟨_, rfl⟩,
          (QRegister.mem_image rSys _).mpr ⟨_, rfl⟩⟩
      · exact batchCnotPairs_mem_sys rSys pairs6 (fun l ↦ idxAx l.succ) wp htail
theorem cnotPairsPerm_axis_outside {kSys : ℕ} (rSys : QRegister kSys n)
    (g : Fin 6 → Fin kSys) (pairs6 : List (Fin 6 × Fin 6))
    (δ : BitAssignment n) (w : Wire n) (hout : ∀ q : Fin 6, rSys (g q) ≠ w) :
    cnotPairsPerm (axisCnotPairs rSys g pairs6) δ w = δ w :=
  cnotPairsPerm_outside _ δ w fun wp hwp ↦ by
    rcases List.mem_map.mp hwp with ⟨p, _, rfl⟩
    exact hout p.2
theorem cnotPairsPerm_axis_apply {kSys : ℕ} (rSys : QRegister kSys n)
    (g : Fin 6 → Fin kSys) (hinj : Function.Injective g) :
    ∀ (pairs6 : List (Fin 6 × Fin 6)) (δ : BitAssignment n) (q : Fin 6),
      cnotPairsPerm (axisCnotPairs rSys g pairs6) δ (rSys (g q)) =
        localPerm6 pairs6 (fun i ↦ δ (rSys (g i))) q
  | [], _, _ => rfl
  | p :: rest, δ, q => by
      dsimp only [axisCnotPairs, List.map, cnotPairsPerm, localPerm6]
      change cnotPairsPerm (axisCnotPairs rSys g rest) _ _ = _
      rw [cnotPairsPerm_axis_apply rSys g hinj rest]
      congr 1; funext i
      by_cases hi : i = p.2
      · subst hi; simp [Function.update_self]
      · have hne_w : rSys (g i) ≠ rSys (g p.2) := fun h ↦ hi (hinj (rSys.wires.injective h))
        simp [Function.update_of_ne hi, Function.update_of_ne hne_w]
theorem cnotPairsPerm_batch_outside {kSys : ℕ} (rSys : QRegister kSys n)
    (pairs6 : List (Fin 6 × Fin 6)) :
    ∀ {L : ℕ} (idxAx : Fin L → Fin 6 → Fin kSys) (δ : BitAssignment n) (w : Wire n),
      (∀ (l : Fin L) (q : Fin 6), rSys (idxAx l q) ≠ w) →
      cnotPairsPerm (batchCnotPairs rSys pairs6 idxAx) δ w = δ w
  | 0, _, _, _, _ => rfl
  | _ + 1, idxAx, δ, w, hout => by
      rw [batchCnotPairs, cnotPairsPerm_append,
        cnotPairsPerm_batch_outside rSys pairs6 (fun l ↦ idxAx l.succ) _ w
          (fun l q ↦ hout l.succ q),
        cnotPairsPerm_axis_outside rSys (idxAx 0) pairs6 δ w (fun q ↦ hout 0 q)]
theorem cnotPairsPerm_batch_apply {kSys : ℕ} (rSys : QRegister kSys n)
    (pairs6 : List (Fin 6 × Fin 6)) :
    ∀ {L : ℕ} (idxAx : Fin L → Fin 6 → Fin kSys),
      Function.Injective (fun p : Fin L × Fin 6 ↦ idxAx p.1 p.2) →
      ∀ (δ : BitAssignment n) (l : Fin L) (q : Fin 6),
        cnotPairsPerm (batchCnotPairs rSys pairs6 idxAx) δ (rSys (idxAx l q)) =
          localPerm6 pairs6 (fun i ↦ δ (rSys (idxAx l i))) q
  | 0, _, _, _, l, _ => Fin.elim0 l
  | _ + 1, idxAx, hinj, δ, l, q => by
      rw [batchCnotPairs, cnotPairsPerm_append]
      let δ₁ := cnotPairsPerm (axisCnotPairs rSys (idxAx 0) pairs6) δ
      have hinj0 : Function.Injective (idxAx 0) := fun a b h ↦
        have hp : ((0, a) : Fin _ × Fin 6) = (0, b) := hinj h
        congrArg Prod.snd hp
      have hinj_succ : Function.Injective (fun p : Fin _ × Fin 6 ↦ idxAx p.1.succ p.2) := by
        rintro ⟨a1, a2⟩ ⟨b1, b2⟩ h
        have hab : ((a1.succ, a2) : Fin _ × Fin 6) = (b1.succ, b2) := hinj h
        have h1 : a1.succ = b1.succ := congrArg Prod.fst hab
        have h2 : a2 = b2 := congrArg Prod.snd hab
        exact Prod.ext (Fin.succ_injective _ h1) h2
      refine Fin.cases ?_ (fun l' ↦ ?_) l
      · rw [cnotPairsPerm_batch_outside rSys pairs6 (fun m ↦ idxAx m.succ) δ₁ (rSys (idxAx 0 q))
          (fun m r heq ↦
            have hp : ((m.succ, r) : Fin _ × Fin 6) = (0, q) := hinj (rSys.wires.injective heq)
            Fin.succ_ne_zero m (congrArg Prod.fst hp))]
        exact cnotPairsPerm_axis_apply rSys (idxAx 0) hinj0 pairs6 δ q
      · rw [cnotPairsPerm_batch_apply rSys pairs6 (fun m ↦ idxAx m.succ) hinj_succ δ₁ l' q]
        congr 1; funext i
        exact cnotPairsPerm_axis_outside rSys (idxAx 0) pairs6 δ (rSys (idxAx l'.succ i))
          (fun r heq ↦
            have hp : ((l'.succ, i) : Fin _ × Fin 6) = (0, r) := hinj (rSys.wires.injective
                heq.symm)
            Fin.succ_ne_zero l' (congrArg Prod.fst hp))
structure ForestSlotConfig (s : ℕ) where
  pairs : List (Fin 6 × Fin 6)
  hne : ∀ p ∈ pairs, p.1 ≠ p.2
  qCin0 : Fin 6
  col0Tail6 : List (Fin 6)
  colRest6 : Fin (3 - s) → List (Fin 6)
  hCinNotTail : qCin0 ∉ col0Tail6
  hTailNodup : col0Tail6.Nodup
  hRestNodup : ∀ r : Fin (3 - s), (colRest6 r).Nodup
  hCinDisjRest : ∀ (r : Fin (3 - s)), qCin0 ∉ colRest6 r
  hTailDisjRest : ∀ (r : Fin (3 - s)) (q : Fin 6), q ∈ col0Tail6 → q ∉ colRest6 r
  hRestDisj : ∀ (r₁ r₂ : Fin (3 - s)), r₁ ≠ r₂ → ∀ q ∈ colRest6 r₁, q ∉ colRest6 r₂
def xorForestBucketsLen (s : ℕ) (cfg : ForestSlotConfig s) (L : ℕ) : List ℕ :=
  ((L - 1) + cfg.col0Tail6.length * L) :: (List.ofFn fun r : Fin (3 - s) ↦ (cfg.colRest6 r).length
      * L)
def xorForestBatchWork (s : ℕ) (cfg : ForestSlotConfig s) (L : ℕ) : ℕ :=
  1 + compressStepsNat (xorForestBucketsLen s cfg L) 0 + (4 - s)
def xorForestBatchTCost (s : ℕ) (cfg : ForestSlotConfig s) (L : ℕ) : ℕ := 4 * compressStepsNat
    (xorForestBucketsLen s cfg L) 0 + finalCarriesNat (xorForestBucketsLen s cfg L) 0 +
    (4 * (4 - s) + 1)
def forestAxisNat (s : ℕ) (cfg : ForestSlotConfig s) (b : Fin 6 → ZMod 2) : ℕ := 2 ^ s *
    ((localPerm6 cfg.pairs b cfg.qCin0).val + (cfg.col0Tail6.map fun q ↦ (localPerm6 cfg.pairs
    b q).val).sum) + ∑ r : Fin (3 - s), 2 ^ (s + (r.val + 1)) *
    ((cfg.colRest6 r).map fun q ↦ (localPerm6 cfg.pairs b q).val).sum
def expandColWires {L kSys : ℕ} (rSys : QRegister kSys n)
    (idxAx : Fin L → Fin 6 → Fin kSys) : List (Fin 6) → List (Wire n)
  | [] => []
  | q :: qs => finMapList (fun l : Fin L ↦ rSys (idxAx l q)) ++ expandColWires rSys idxAx qs
theorem expandColWires_length {L kSys : ℕ} (rSys : QRegister kSys n)
    (idxAx : Fin L → Fin 6 → Fin kSys) :
    ∀ (qs : List (Fin 6)), (expandColWires rSys idxAx qs).length = qs.length * L
  | [] => by simp [expandColWires]
  | q :: qs => by
      simp only [expandColWires, List.length_append, finMapList_length,
        expandColWires_length rSys idxAx qs, List.length_cons]
      ring
theorem finMapList_map_length_eq_ofFn {α : Type*} :
    ∀ {m : ℕ} (g : Fin m → List α),
      (finMapList g).map List.length = List.ofFn (fun r : Fin m ↦ (g r).length)
  | 0, _ => by
      have h0 : finMapList (L := 0) = fun (_ : Fin 0 → List α) ↦ ([] : List (List α)) := by
        funext f; exact List.eq_nil_of_length_eq_zero (finMapList_length f)
      simp [h0]
  | m + 1, g => by
      have hcons : finMapList g = g 0 :: finMapList (fun r : Fin m ↦ g r.succ) := by
        conv_lhs => unfold finMapList
      rw [hcons, List.map_cons, finMapList_map_length_eq_ofFn (fun r ↦ g r.succ), List.ofFn_succ]
theorem mem_expandColWires {L kSys : ℕ} (rSys : QRegister kSys n)
    (idxAx : Fin L → Fin 6 → Fin kSys) :
    ∀ (qs : List (Fin 6)) (w : Wire n),
      w ∈ expandColWires rSys idxAx qs ↔ ∃ q ∈ qs, ∃ l : Fin L, rSys (idxAx l q) = w
  | [], w => by simp [expandColWires]
  | q :: qs, w => by
      simp only [expandColWires, List.mem_append, mem_finMapList,
        mem_expandColWires rSys idxAx qs, List.mem_cons]
      constructor
      · rintro (⟨l, rfl⟩ | ⟨q', hq', l, rfl⟩)
        · exact ⟨q, Or.inl rfl, l, rfl⟩
        · exact ⟨q', Or.inr hq', l, rfl⟩
      · rintro ⟨q', rfl | hq', l, rfl⟩
        · exact Or.inl ⟨l, rfl⟩
        · exact Or.inr ⟨q', hq', l, rfl⟩
theorem expandColWires_nodup {L kSys : ℕ} (rSys : QRegister kSys n)
    (idxAx : Fin L → Fin 6 → Fin kSys)
    (hinj : Function.Injective (fun p : Fin L × Fin 6 ↦ idxAx p.1 p.2)) :
    ∀ (qs : List (Fin 6)), qs.Nodup → (expandColWires rSys idxAx qs).Nodup
  | [], _ => List.nodup_nil
  | q :: qs, hnd => by
      obtain ⟨hq_not, hqs_nd⟩ := List.nodup_cons.mp hnd
      rw [expandColWires, List.nodup_append]
      refine ⟨finMapList_nodup (fun l₁ l₂ h ↦
          have hp : ((l₁, q) : Fin L × Fin 6) = (l₂, q) := hinj (rSys.wires.injective h)
          congrArg Prod.fst hp),
        expandColWires_nodup rSys idxAx hinj qs hqs_nd,
        fun x hx y hy hxy ↦ ?_⟩
      subst hxy
      rcases mem_finMapList.mp hx with ⟨l₁, rfl⟩
      rcases (mem_expandColWires rSys idxAx qs _).mp hy with ⟨q', hq', l₂, heq⟩
      have hp : ((l₂, q') : Fin L × Fin 6) = (l₁, q) := hinj (rSys.wires.injective heq)
      have hq_eq : q' = q := congrArg Prod.snd hp
      exact hq_not (hq_eq ▸ hq')
theorem wireListSum_expandColWires {L kSys : ℕ} (rSys : QRegister kSys n)
    (idxAx : Fin L → Fin 6 → Fin kSys) (δ : BitAssignment n) :
    ∀ (qs : List (Fin 6)),
      wireListSum (expandColWires rSys idxAx qs) δ =
        ∑ l : Fin L, (qs.map fun q ↦ (δ (rSys (idxAx l q))).val).sum
  | [] => by simp [expandColWires]
  | q :: qs => by
      rw [expandColWires, wireListSum_append, wireListSum_finMapList,
        wireListSum_expandColWires rSys idxAx δ qs, ← Finset.sum_add_distrib]
      rfl
theorem weightedBuckets_forest_eq {L kSys : ℕ} (s : ℕ) (cfg : ForestSlotConfig s)
    (hL : 1 ≤ L) (rSys : QRegister kSys n) (idxAx : Fin L → Fin 6 → Fin kSys)
    (hinj : Function.Injective (fun p : Fin L × Fin 6 ↦ idxAx p.1 p.2))
    (γ : BitAssignment kSys) :
    let β₁ := cnotPairsPerm (batchCnotPairs rSys cfg.pairs idxAx) (canonAssign rSys γ)
    let wCin0 : Wire n := rSys (idxAx ⟨0, hL⟩ cfg.qCin0)
    let col0Bucket : List (Wire n) :=
      finMapList (fun i : Fin (L - 1) ↦ rSys (idxAx ⟨i.val + 1, by omega⟩ cfg.qCin0)) ++
        expandColWires rSys idxAx cfg.col0Tail6
    let colRest : Fin (3 - s) → List (Wire n) :=
      fun r ↦ expandColWires rSys idxAx (cfg.colRest6 r)
    2 ^ s * ((β₁ wCin0).val + weightedBucketsVal (col0Bucket :: finMapList colRest) β₁) =
      ∑ l : Fin L, forestAxisNat s cfg (fun i ↦ γ (idxAx l i)) := by
  intro β₁ wCin0 col0Bucket colRest
  have hβ₁ : ∀ (l : Fin L) (q : Fin 6),
      β₁ (rSys (idxAx l q)) = localPerm6 cfg.pairs (fun i ↦ γ (idxAx l i)) q := by
    intro l q
    dsimp only [β₁]
    rw [cnotPairsPerm_batch_apply rSys cfg.pairs idxAx hinj]
    congr 1; funext i
    exact canonAssign_apply_sys rSys γ (idxAx l i)
  rw [weightedBucketsVal]
  have hcol0 : (β₁ wCin0).val + wireListSum col0Bucket β₁ = ∑ l : Fin L, ((β₁ (rSys (idxAx l
      cfg.qCin0))).val + (cfg.col0Tail6.map fun q ↦ (β₁ (rSys (idxAx l q))).val).sum) := by
    dsimp only [wCin0, col0Bucket]
    rw [wireListSum_append, ← add_assoc,
      head_add_wireListSum_tail hL (fun l : Fin L ↦ rSys (idxAx l cfg.qCin0)) β₁,
      wireListSum_expandColWires, ← Finset.sum_add_distrib]
  rw [← add_assoc, hcol0, weightedBucketsVal_finMapList]
  simp only [colRest, wireListSum_expandColWires]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  have hswap : (∑ r : Fin (3 - s), 2 ^ s * (2 * (2 ^ r.val * ∑ l : Fin L, ((cfg.colRest6
      r).map fun q ↦ (β₁ (rSys (idxAx l q))).val).sum))) = ∑ l : Fin L, ∑ r : Fin (3 - s), 2 ^
      (s + (r.val + 1)) * ((cfg.colRest6 r).map fun q ↦ (β₁ (rSys (idxAx l q))).val).sum := by
    have h1 : ∀ r : Fin (3 - s),
        2 ^ s * (2 * (2 ^ r.val * ∑ l : Fin L,
            ((cfg.colRest6 r).map fun q ↦ (β₁ (rSys (idxAx l q))).val).sum)) =
          ∑ l : Fin L, 2 ^ (s + (r.val + 1)) *
            ((cfg.colRest6 r).map fun q ↦ (β₁ (rSys (idxAx l q))).val).sum := fun r ↦ by
      have hp : 2 ^ (s + (r.val + 1)) = 2 ^ s * (2 * 2 ^ r.val) := by
        rw [Nat.add_comm (r.val) 1, ← Nat.add_assoc, pow_add, pow_add, pow_one]; ring
      rw [hp, ← Finset.mul_sum]; ring
    simp_rw [h1]
    exact Finset.sum_comm
  rw [hswap, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  dsimp only [forestAxisNat]
  simp_rw [hβ₁ l]
def xorForestBatchFwdDyn {kSys mWork : ℕ} (v : Var) (s : ℕ) (cfg : ForestSlotConfig s) (L : ℕ)
    (hs : s ≤ 3) (hL : 1 ≤ L) (hm : xorForestBatchWork s cfg L ≤ mWork)
    (rSys : QRegister kSys n) (rPG : QRegister 7 n) (rWork : QRegister mWork n)
    (hdisj_SP : rSys.DisjointWires rPG) (hdisj_SW : rSys.DisjointWires rWork)
    (hdisj_PW : rPG.DisjointWires rWork) (idxAx : Fin L → Fin 6 → Fin kSys) (hinj_ax :
    Function.Injective (fun p : Fin L × Fin 6 ↦ idxAx p.1 p.2)) : DynamicCircuit Var n :=
  let wpairs := batchCnotPairs rSys cfg.pairs idxAx
  have hne_fwd : ∀ wp ∈ wpairs, wp.1 ≠ wp.2 := batchCnotPairs_hne rSys cfg.pairs cfg.hne idxAx
      hinj_ax
  have hne_inv : ∀ wp ∈ wpairs.reverse, wp.1 ≠ wp.2 := fun wp hwp ↦ hne_fwd wp (List.mem_reverse.mp
      hwp)
  let c_xor_fwd : Circuit n := cnotPairsCircuit wpairs hne_fwd
  let c_xor_inv : Circuit n := cnotPairsCircuit wpairs.reverse hne_inv
  let col0Bucket : List (Wire n) :=
    finMapList (fun i : Fin (L - 1) ↦ rSys (idxAx ⟨i.val + 1, by omega⟩ cfg.qCin0)) ++
      expandColWires rSys idxAx cfg.col0Tail6
  let colRest : Fin (3 - s) → List (Wire n) :=
    fun r ↦ expandColWires rSys idxAx (cfg.colRest6 r)
  let buckets : List (List (Wire n)) := col0Bucket :: finMapList colRest
  have hmap_len : buckets.map List.length = xorForestBucketsLen s cfg L := by
    simp only [buckets, xorForestBucketsLen, List.map_cons, col0Bucket, List.length_append,
      finMapList_length, finMapList_map_length_eq_ofFn, expandColWires_length, colRest]
  have hsteps_eq : compressStepsCount buckets 0 = compressStepsNat (xorForestBucketsLen s cfg L) 0
      := by
    rw [compressStepsCount_eq_nat, hmap_len]
  have hfit_csa : 0 + compressStepsCount buckets 0 ≤ mWork := by
    dsimp only [xorForestBatchWork] at hm; rw [hsteps_eq]; omega
  have hB_nodup : ∀ B ∈ buckets, B.Nodup := fun B hB ↦ by
    rcases List.mem_cons.mp hB with rfl | hB_rest
    · rw [List.nodup_append]
      refine ⟨finMapList_nodup (fun i₁ i₂ h ↦ by
          have hp : ((⟨i₁.val + 1, by omega⟩, cfg.qCin0) : Fin L × Fin 6) =
              (⟨i₂.val + 1, by omega⟩, cfg.qCin0) := hinj_ax (rSys.wires.injective h)
          have hv : i₁.val + 1 = i₂.val + 1 := congrArg (fun p : Fin L × Fin 6 ↦ p.1.val) hp
          exact Fin.ext (by omega)),
        expandColWires_nodup rSys idxAx hinj_ax cfg.col0Tail6 cfg.hTailNodup,
        fun x hx y hy hxy ↦ ?_⟩
      subst hxy
      rcases mem_finMapList.mp hx with ⟨i, rfl⟩
      rcases (mem_expandColWires rSys idxAx cfg.col0Tail6 _).mp hy with ⟨q', hq', l, heq⟩
      have hp : ((l, q') : Fin L × Fin 6) = (⟨i.val + 1, by omega⟩, cfg.qCin0) :=
        hinj_ax (rSys.wires.injective heq)
      have hq_eq : q' = cfg.qCin0 := congrArg Prod.snd hp
      exact cfg.hCinNotTail (hq_eq ▸ hq')
    · rcases mem_finMapList.mp hB_rest with ⟨r, rfl⟩
      exact expandColWires_nodup rSys idxAx hinj_ax (cfg.colRest6 r) (cfg.hRestNodup r)
  have hB_disj : buckets.Pairwise fun B₁ B₂ ↦ ∀ x ∈ B₁, x ∉ B₂ := by
    rw [List.pairwise_cons]
    refine ⟨fun B₂ hB₂ x hx₁ hx₂ ↦ ?_,
      buckets_pairwise_finMapList colRest fun r₁ r₂ hne x hx₁ hx₂ ↦ ?_⟩
    · rcases mem_finMapList.mp hB₂ with ⟨r, rfl⟩
      rcases (mem_expandColWires rSys idxAx (cfg.colRest6 r) x).mp hx₂ with ⟨q₂, hq₂, l₂, rfl⟩
      rcases List.mem_append.mp hx₁ with hx_cin | hx_tail
      · rcases mem_finMapList.mp hx_cin with ⟨i, heq⟩
        have hp : ((⟨i.val + 1, by omega⟩, cfg.qCin0) : Fin L × Fin 6) = (l₂, q₂) :=
          hinj_ax (rSys.wires.injective heq)
        have hq_eq : q₂ = cfg.qCin0 := (congrArg Prod.snd hp).symm
        exact cfg.hCinDisjRest r (hq_eq ▸ hq₂)
      · rcases (mem_expandColWires rSys idxAx cfg.col0Tail6 _).mp hx_tail with ⟨q₁, hq₁, l₁, heq⟩
        have hp : ((l₁, q₁) : Fin L × Fin 6) = (l₂, q₂) := hinj_ax (rSys.wires.injective heq)
        have hq_eq : q₂ = q₁ := (congrArg Prod.snd hp).symm
        exact cfg.hTailDisjRest r q₁ hq₁ (hq_eq ▸ hq₂)
    · rcases (mem_expandColWires rSys idxAx (cfg.colRest6 r₁) x).mp hx₁ with ⟨q₁, hq₁, l₁, rfl⟩
      rcases (mem_expandColWires rSys idxAx (cfg.colRest6 r₂) _).mp hx₂ with ⟨q₂, hq₂, l₂, heq⟩
      have hp : ((l₂, q₂) : Fin L × Fin 6) = (l₁, q₁) := hinj_ax (rSys.wires.injective heq)
      have hq_eq : q₂ = q₁ := congrArg Prod.snd hp
      exact cfg.hRestDisj r₁ r₂ hne q₁ hq₁ (hq_eq ▸ hq₂)
  have hB_sys : ∀ B ∈ buckets, ∀ x ∈ B, x ∈ rSys.image := fun B hB x hx ↦ by
    rcases List.mem_cons.mp hB with rfl | hB_rest
    · rcases List.mem_append.mp hx with hx_cin | hx_tail
      · rcases mem_finMapList.mp hx_cin with ⟨_, rfl⟩
        exact (QRegister.mem_image rSys _).mpr ⟨_, rfl⟩
      · rcases (mem_expandColWires rSys idxAx cfg.col0Tail6 x).mp hx_tail with ⟨_, _, _, rfl⟩
        exact (QRegister.mem_image rSys _).mpr ⟨_, rfl⟩
    · rcases mem_finMapList.mp hB_rest with ⟨r, rfl⟩
      rcases (mem_expandColWires rSys idxAx (cfg.colRest6 r) x).mp hx with ⟨_, _, _, rfl⟩
      exact (QRegister.mem_image rSys _).mpr ⟨_, rfl⟩
  have hB_anc : ∀ B ∈ buckets, ∀ x ∈ B, x ∉ rWork.image := fun B hB x hx hm_w ↦ by
    rcases (QRegister.mem_image rSys x).mp (hB_sys B hB x hx) with ⟨i, rfl⟩
    rcases (QRegister.mem_image rWork _).mp hm_w with ⟨k, hk⟩
    exact hdisj_SW.ne i k hk.symm
  have hB_PG : ∀ B ∈ buckets, ∀ x ∈ B, x ∉ rPG.image := fun B hB x hx hm_pg ↦ by
    rcases (QRegister.mem_image rSys x).mp (hB_sys B hB x hx) with ⟨i, rfl⟩
    rcases (QRegister.mem_image rPG _).mp hm_pg with ⟨k, hk⟩
    exact hdisj_SP.ne i k hk.symm
  let out := compressBuckets rWork buckets 0 hfit_csa hB_nodup hB_disj hB_anc
  have hspec := compressBuckets_spec rPG.image rWork
    (disjWires_image (QRegExt.disjointWires_symm hdisj_PW)) buckets 0 hfit_csa hB_nodup hB_disj
      hB_anc hB_PG
  let st := out.steps.length
  have _hst : st = compressStepsNat (xorForestBucketsLen s cfg L) 0 := hspec.2.1.trans hsteps_eq
  have _hm' : 1 + st + (4 - s) ≤ mWork := by dsimp only [xorForestBatchWork] at hm; omega
  let rGid : QRegister (4 - s) n := rWork.slice (0 + st) (4 - s) (by omega)
  let wZero : Wire n := rWork ⟨st + (4 - s), by omega⟩
  have hsw_len : out.sumWires.length = 4 - s := by
    rw [hspec.1]
    simp only [buckets, List.length_cons, finMapList_length]
    omega
  let wCin0 : Wire n := rSys (idxAx ⟨0, hL⟩ cfg.qCin0)
  let tWires : List (Wire n) := out.carries
  let rMidPG : QRegister (4 - s) n := rPG.slice s (4 - s) (by omega)
  let uWires : Fin (4 - s) → Wire n := fun j ↦
    optWireOrZero wZero (out.sumWires.get ⟨j.val, by omega⟩)
  have hu_T : ∀ j, uWires j ∉ rMidPG.image := fun j hm_t ↦ by
    have hm_pg : uWires j ∈ rPG.image := QRegister.image_compose_subset rPG _ hm_t
    dsimp only [uWires] at hm_pg
    cases hget : out.sumWires.get ⟨j.val, by omega⟩ with
    | none =>
        rw [hget] at hm_pg; dsimp only [optWireOrZero, wZero] at hm_pg
        rcases (QRegister.mem_image rPG _).mp hm_pg with ⟨i, hi⟩
        exact hdisj_PW.ne i ⟨st + (4 - s), by omega⟩ hi
    | some w =>
        rw [hget] at hm_pg; dsimp only [optWireOrZero] at hm_pg
        rcases hspec.2.2.2.2.1 _ (List.get_mem _ _) w hget with ⟨B, hB, hwB⟩ | ⟨k, hk, _, _, rfl⟩
        · exact hB_PG B hB w hwB hm_pg
        · rcases (QRegister.mem_image rPG _).mp hm_pg with ⟨i, hi⟩
          exact hdisj_PW.ne i ⟨k, hk⟩ hi
  have hu_C : ∀ j, uWires j ∉ rGid.image := fun j hm_c ↦ by
    rcases (QRegister.mem_image rGid _).mp hm_c with ⟨i, hi⟩
    have hi' : rGid i = rWork ⟨st + i.val, by omega⟩ := by
      rw [QRegister.slice_apply]; exact congrArg rWork (Fin.ext (by simp))
    rw [hi'] at hi
    dsimp only [uWires] at hi
    cases hget : out.sumWires.get ⟨j.val, by omega⟩ with
    | none =>
        rw [hget] at hi; dsimp only [optWireOrZero, wZero] at hi
        have hv := congrArg Fin.val (rWork.wires.injective hi); dsimp at hv; omega
    | some w =>
        rw [hget] at hi; dsimp only [optWireOrZero] at hi
        rcases hspec.2.2.2.2.1 _ (List.get_mem _ _) w hget with ⟨B, hB, hwB⟩ | ⟨k, hk, _, hk_lt,
            rfl⟩
        · exact hB_anc B hB w hwB ((QRegister.mem_image rWork _).mpr ⟨_, hi⟩)
        · have hv := congrArg Fin.val (rWork.wires.injective hi)
          dsimp at hv; have := hspec.2.1; omega
  have hdisj_TC : rMidPG.DisjointWires rGid := (hdisj_PW.compose_left _).compose_right _
  have hwcin_not_B : ∀ B ∈ buckets, wCin0 ∉ B := fun B hB hmem ↦ by
    rcases List.mem_cons.mp hB with rfl | hB_rest
    · rcases List.mem_append.mp hmem with hcin | htail
      · rcases mem_finMapList.mp hcin with ⟨i, heq⟩
        have hp : ((⟨i.val + 1, by omega⟩, cfg.qCin0) : Fin L × Fin 6) = (⟨0, hL⟩, cfg.qCin0) :=
          hinj_ax (rSys.wires.injective heq)
        have hv : i.val + 1 = 0 := congrArg (fun p : Fin L × Fin 6 ↦ p.1.val) hp
        omega
      · rcases (mem_expandColWires rSys idxAx cfg.col0Tail6 _).mp htail with ⟨q', hq', l, heq⟩
        have hp : ((l, q') : Fin L × Fin 6) = (⟨0, hL⟩, cfg.qCin0) :=
          hinj_ax (rSys.wires.injective heq)
        have hq_eq : q' = cfg.qCin0 := congrArg Prod.snd hp
        exact cfg.hCinNotTail (hq_eq ▸ hq')
    · rcases mem_finMapList.mp hB_rest with ⟨r, rfl⟩
      rcases (mem_expandColWires rSys idxAx (cfg.colRest6 r) _).mp hmem with ⟨q', hq', l, heq⟩
      have hp : ((l, q') : Fin L × Fin 6) = (⟨0, hL⟩, cfg.qCin0) :=
        hinj_ax (rSys.wires.injective heq)
      have hq_eq : q' = cfg.qCin0 := congrArg Prod.snd hp
      exact cfg.hCinDisjRest r (hq_eq ▸ hq')
  have hcin_u : ∀ j, wCin0 ≠ uWires j := fun j heq ↦ by
    dsimp only [uWires] at heq
    cases hget : out.sumWires.get ⟨j.val, by omega⟩ with
    | none =>
        rw [hget] at heq; dsimp only [optWireOrZero, wZero, wCin0] at heq
        exact hdisj_SW.ne _ ⟨st + (4 - s), by omega⟩ heq
    | some w =>
        rw [hget] at heq; dsimp only [optWireOrZero] at heq
        rcases hspec.2.2.2.2.1 _ (List.get_mem _ _) w hget with ⟨B, hB, hwB⟩ | ⟨k, hk, _, _, rfl⟩
        · rw [← heq] at hwB
          exact hwcin_not_B B hB hwB
        · exact hdisj_SW.ne _ ⟨k, hk⟩ heq
  have hcin_T : wCin0 ∉ rMidPG.image := fun hm_t ↦ by
    rcases (QRegister.mem_image rPG _).mp (QRegister.image_compose_subset rPG _ hm_t) with ⟨i, hi⟩
    exact hdisj_SP.ne _ i hi.symm
  have hcin_C : wCin0 ∉ rGid.image := fun hm_c ↦ by
    rcases (QRegister.mem_image rWork _).mp (QRegister.image_compose_subset rWork _ hm_c) with ⟨k,
        hk⟩
    exact hdisj_SW.ne _ k hk.symm
  (DynamicCircuit.circuit c_xor_fwd).seq
    ((symWrapDynList v out.steps
      ((DynamicCircuit.circuit (tList tWires)).seq
        ((gidneyApexChainDyn v false (4 - s) uWires rMidPG rGid wCin0
            hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C).seq
          (DynamicCircuit.circuit Circuit.identity)))).seq
      (DynamicCircuit.circuit c_xor_inv))
def xorForestBatchInvDyn {kSys mWork : ℕ} (v : Var) (s : ℕ) (cfg : ForestSlotConfig s) (L : ℕ)
    (hs : s ≤ 3) (hL : 1 ≤ L) (hm : xorForestBatchWork s cfg L ≤ mWork)
    (rSys : QRegister kSys n) (rPG : QRegister 7 n) (rWork : QRegister mWork n)
    (hdisj_SP : rSys.DisjointWires rPG) (hdisj_SW : rSys.DisjointWires rWork)
    (hdisj_PW : rPG.DisjointWires rWork) (idxAx : Fin L → Fin 6 → Fin kSys) (hinj_ax :
    Function.Injective (fun p : Fin L × Fin 6 ↦ idxAx p.1 p.2)) : DynamicCircuit Var n :=
  let wpairs := batchCnotPairs rSys cfg.pairs idxAx
  have hne_fwd : ∀ wp ∈ wpairs, wp.1 ≠ wp.2 := batchCnotPairs_hne rSys cfg.pairs cfg.hne idxAx
      hinj_ax
  have hne_inv : ∀ wp ∈ wpairs.reverse, wp.1 ≠ wp.2 := fun wp hwp ↦ hne_fwd wp (List.mem_reverse.mp
      hwp)
  let c_xor_fwd : Circuit n := cnotPairsCircuit wpairs hne_fwd
  let c_xor_inv : Circuit n := cnotPairsCircuit wpairs.reverse hne_inv
  let col0Bucket : List (Wire n) :=
    finMapList (fun i : Fin (L - 1) ↦ rSys (idxAx ⟨i.val + 1, by omega⟩ cfg.qCin0)) ++
      expandColWires rSys idxAx cfg.col0Tail6
  let colRest : Fin (3 - s) → List (Wire n) :=
    fun r ↦ expandColWires rSys idxAx (cfg.colRest6 r)
  let buckets : List (List (Wire n)) := col0Bucket :: finMapList colRest
  have hmap_len : buckets.map List.length = xorForestBucketsLen s cfg L := by
    simp only [buckets, xorForestBucketsLen, List.map_cons, col0Bucket, List.length_append,
      finMapList_length, finMapList_map_length_eq_ofFn, expandColWires_length, colRest]
  have hsteps_eq : compressStepsCount buckets 0 = compressStepsNat (xorForestBucketsLen s cfg L) 0
      := by
    rw [compressStepsCount_eq_nat, hmap_len]
  have hfit_csa : 0 + compressStepsCount buckets 0 ≤ mWork := by
    dsimp only [xorForestBatchWork] at hm; rw [hsteps_eq]; omega
  have hB_nodup : ∀ B ∈ buckets, B.Nodup := fun B hB ↦ by
    rcases List.mem_cons.mp hB with rfl | hB_rest
    · rw [List.nodup_append]
      refine ⟨finMapList_nodup (fun i₁ i₂ h ↦ by
          have hp : ((⟨i₁.val + 1, by omega⟩, cfg.qCin0) : Fin L × Fin 6) =
              (⟨i₂.val + 1, by omega⟩, cfg.qCin0) := hinj_ax (rSys.wires.injective h)
          have hv : i₁.val + 1 = i₂.val + 1 := congrArg (fun p : Fin L × Fin 6 ↦ p.1.val) hp
          exact Fin.ext (by omega)),
        expandColWires_nodup rSys idxAx hinj_ax cfg.col0Tail6 cfg.hTailNodup,
        fun x hx y hy hxy ↦ ?_⟩
      subst hxy
      rcases mem_finMapList.mp hx with ⟨i, rfl⟩
      rcases (mem_expandColWires rSys idxAx cfg.col0Tail6 _).mp hy with ⟨q', hq', l, heq⟩
      have hp : ((l, q') : Fin L × Fin 6) = (⟨i.val + 1, by omega⟩, cfg.qCin0) :=
        hinj_ax (rSys.wires.injective heq)
      have hq_eq : q' = cfg.qCin0 := congrArg Prod.snd hp
      exact cfg.hCinNotTail (hq_eq ▸ hq')
    · rcases mem_finMapList.mp hB_rest with ⟨r, rfl⟩
      exact expandColWires_nodup rSys idxAx hinj_ax (cfg.colRest6 r) (cfg.hRestNodup r)
  have hB_disj : buckets.Pairwise fun B₁ B₂ ↦ ∀ x ∈ B₁, x ∉ B₂ := by
    rw [List.pairwise_cons]
    refine ⟨fun B₂ hB₂ x hx₁ hx₂ ↦ ?_,
      buckets_pairwise_finMapList colRest fun r₁ r₂ hne x hx₁ hx₂ ↦ ?_⟩
    · rcases mem_finMapList.mp hB₂ with ⟨r, rfl⟩
      rcases (mem_expandColWires rSys idxAx (cfg.colRest6 r) x).mp hx₂ with ⟨q₂, hq₂, l₂, rfl⟩
      rcases List.mem_append.mp hx₁ with hx_cin | hx_tail
      · rcases mem_finMapList.mp hx_cin with ⟨i, heq⟩
        have hp : ((⟨i.val + 1, by omega⟩, cfg.qCin0) : Fin L × Fin 6) = (l₂, q₂) :=
          hinj_ax (rSys.wires.injective heq)
        have hq_eq : q₂ = cfg.qCin0 := (congrArg Prod.snd hp).symm
        exact cfg.hCinDisjRest r (hq_eq ▸ hq₂)
      · rcases (mem_expandColWires rSys idxAx cfg.col0Tail6 _).mp hx_tail with ⟨q₁, hq₁, l₁, heq⟩
        have hp : ((l₁, q₁) : Fin L × Fin 6) = (l₂, q₂) := hinj_ax (rSys.wires.injective heq)
        have hq_eq : q₂ = q₁ := (congrArg Prod.snd hp).symm
        exact cfg.hTailDisjRest r q₁ hq₁ (hq_eq ▸ hq₂)
    · rcases (mem_expandColWires rSys idxAx (cfg.colRest6 r₁) x).mp hx₁ with ⟨q₁, hq₁, l₁, rfl⟩
      rcases (mem_expandColWires rSys idxAx (cfg.colRest6 r₂) _).mp hx₂ with ⟨q₂, hq₂, l₂, heq⟩
      have hp : ((l₂, q₂) : Fin L × Fin 6) = (l₁, q₁) := hinj_ax (rSys.wires.injective heq)
      have hq_eq : q₂ = q₁ := congrArg Prod.snd hp
      exact cfg.hRestDisj r₁ r₂ hne q₁ hq₁ (hq_eq ▸ hq₂)
  have hB_sys : ∀ B ∈ buckets, ∀ x ∈ B, x ∈ rSys.image := fun B hB x hx ↦ by
    rcases List.mem_cons.mp hB with rfl | hB_rest
    · rcases List.mem_append.mp hx with hx_cin | hx_tail
      · rcases mem_finMapList.mp hx_cin with ⟨_, rfl⟩
        exact (QRegister.mem_image rSys _).mpr ⟨_, rfl⟩
      · rcases (mem_expandColWires rSys idxAx cfg.col0Tail6 x).mp hx_tail with ⟨_, _, _, rfl⟩
        exact (QRegister.mem_image rSys _).mpr ⟨_, rfl⟩
    · rcases mem_finMapList.mp hB_rest with ⟨r, rfl⟩
      rcases (mem_expandColWires rSys idxAx (cfg.colRest6 r) x).mp hx with ⟨_, _, _, rfl⟩
      exact (QRegister.mem_image rSys _).mpr ⟨_, rfl⟩
  have hB_anc : ∀ B ∈ buckets, ∀ x ∈ B, x ∉ rWork.image := fun B hB x hx hm_w ↦ by
    rcases (QRegister.mem_image rSys x).mp (hB_sys B hB x hx) with ⟨i, rfl⟩
    rcases (QRegister.mem_image rWork _).mp hm_w with ⟨k, hk⟩
    exact hdisj_SW.ne i k hk.symm
  have hB_PG : ∀ B ∈ buckets, ∀ x ∈ B, x ∉ rPG.image := fun B hB x hx hm_pg ↦ by
    rcases (QRegister.mem_image rSys x).mp (hB_sys B hB x hx) with ⟨i, rfl⟩
    rcases (QRegister.mem_image rPG _).mp hm_pg with ⟨k, hk⟩
    exact hdisj_SP.ne i k hk.symm
  let out := compressBuckets rWork buckets 0 hfit_csa hB_nodup hB_disj hB_anc
  have hspec := compressBuckets_spec rPG.image rWork
    (disjWires_image (QRegExt.disjointWires_symm hdisj_PW)) buckets 0 hfit_csa hB_nodup hB_disj
      hB_anc hB_PG
  let st := out.steps.length
  have _hst : st = compressStepsNat (xorForestBucketsLen s cfg L) 0 := hspec.2.1.trans hsteps_eq
  have _hm' : 1 + st + (4 - s) ≤ mWork := by dsimp only [xorForestBatchWork] at hm; omega
  let rGid : QRegister (4 - s) n := rWork.slice (0 + st) (4 - s) (by omega)
  let wZero : Wire n := rWork ⟨st + (4 - s), by omega⟩
  have hsw_len : out.sumWires.length = 4 - s := by
    rw [hspec.1]
    simp only [buckets, List.length_cons, finMapList_length]
    omega
  let wCin0 : Wire n := rSys (idxAx ⟨0, hL⟩ cfg.qCin0)
  let tWires : List (Wire n) := out.carries
  let rMidPG : QRegister (4 - s) n := rPG.slice s (4 - s) (by omega)
  let uWires : Fin (4 - s) → Wire n := fun j ↦
    optWireOrZero wZero (out.sumWires.get ⟨j.val, by omega⟩)
  have hu_T : ∀ j, uWires j ∉ rMidPG.image := fun j hm_t ↦ by
    have hm_pg : uWires j ∈ rPG.image := QRegister.image_compose_subset rPG _ hm_t
    dsimp only [uWires] at hm_pg
    cases hget : out.sumWires.get ⟨j.val, by omega⟩ with
    | none =>
        rw [hget] at hm_pg; dsimp only [optWireOrZero, wZero] at hm_pg
        rcases (QRegister.mem_image rPG _).mp hm_pg with ⟨i, hi⟩
        exact hdisj_PW.ne i ⟨st + (4 - s), by omega⟩ hi
    | some w =>
        rw [hget] at hm_pg; dsimp only [optWireOrZero] at hm_pg
        rcases hspec.2.2.2.2.1 _ (List.get_mem _ _) w hget with ⟨B, hB, hwB⟩ | ⟨k, hk, _, _, rfl⟩
        · exact hB_PG B hB w hwB hm_pg
        · rcases (QRegister.mem_image rPG _).mp hm_pg with ⟨i, hi⟩
          exact hdisj_PW.ne i ⟨k, hk⟩ hi
  have hu_C : ∀ j, uWires j ∉ rGid.image := fun j hm_c ↦ by
    rcases (QRegister.mem_image rGid _).mp hm_c with ⟨i, hi⟩
    have hi' : rGid i = rWork ⟨st + i.val, by omega⟩ := by
      rw [QRegister.slice_apply]; exact congrArg rWork (Fin.ext (by simp))
    rw [hi'] at hi
    dsimp only [uWires] at hi
    cases hget : out.sumWires.get ⟨j.val, by omega⟩ with
    | none =>
        rw [hget] at hi; dsimp only [optWireOrZero, wZero] at hi
        have hv := congrArg Fin.val (rWork.wires.injective hi); dsimp at hv; omega
    | some w =>
        rw [hget] at hi; dsimp only [optWireOrZero] at hi
        rcases hspec.2.2.2.2.1 _ (List.get_mem _ _) w hget with ⟨B, hB, hwB⟩ | ⟨k, hk, _, hk_lt,
            rfl⟩
        · exact hB_anc B hB w hwB ((QRegister.mem_image rWork _).mpr ⟨_, hi⟩)
        · have hv := congrArg Fin.val (rWork.wires.injective hi)
          dsimp at hv; have := hspec.2.1; omega
  have hdisj_TC : rMidPG.DisjointWires rGid := (hdisj_PW.compose_left _).compose_right _
  have hwcin_not_B : ∀ B ∈ buckets, wCin0 ∉ B := fun B hB hmem ↦ by
    rcases List.mem_cons.mp hB with rfl | hB_rest
    · rcases List.mem_append.mp hmem with hcin | htail
      · rcases mem_finMapList.mp hcin with ⟨i, heq⟩
        have hp : ((⟨i.val + 1, by omega⟩, cfg.qCin0) : Fin L × Fin 6) = (⟨0, hL⟩, cfg.qCin0) :=
          hinj_ax (rSys.wires.injective heq)
        have hv : i.val + 1 = 0 := congrArg (fun p : Fin L × Fin 6 ↦ p.1.val) hp
        omega
      · rcases (mem_expandColWires rSys idxAx cfg.col0Tail6 _).mp htail with ⟨q', hq', l, heq⟩
        have hp : ((l, q') : Fin L × Fin 6) = (⟨0, hL⟩, cfg.qCin0) :=
          hinj_ax (rSys.wires.injective heq)
        have hq_eq : q' = cfg.qCin0 := congrArg Prod.snd hp
        exact cfg.hCinNotTail (hq_eq ▸ hq')
    · rcases mem_finMapList.mp hB_rest with ⟨r, rfl⟩
      rcases (mem_expandColWires rSys idxAx (cfg.colRest6 r) _).mp hmem with ⟨q', hq', l, heq⟩
      have hp : ((l, q') : Fin L × Fin 6) = (⟨0, hL⟩, cfg.qCin0) :=
        hinj_ax (rSys.wires.injective heq)
      have hq_eq : q' = cfg.qCin0 := congrArg Prod.snd hp
      exact cfg.hCinDisjRest r (hq_eq ▸ hq')
  have hcin_u : ∀ j, wCin0 ≠ uWires j := fun j heq ↦ by
    dsimp only [uWires] at heq
    cases hget : out.sumWires.get ⟨j.val, by omega⟩ with
    | none =>
        rw [hget] at heq; dsimp only [optWireOrZero, wZero, wCin0] at heq
        exact hdisj_SW.ne _ ⟨st + (4 - s), by omega⟩ heq
    | some w =>
        rw [hget] at heq; dsimp only [optWireOrZero] at heq
        rcases hspec.2.2.2.2.1 _ (List.get_mem _ _) w hget with ⟨B, hB, hwB⟩ | ⟨k, hk, _, _, rfl⟩
        · rw [← heq] at hwB
          exact hwcin_not_B B hB hwB
        · exact hdisj_SW.ne _ ⟨k, hk⟩ heq
  have hcin_T : wCin0 ∉ rMidPG.image := fun hm_t ↦ by
    rcases (QRegister.mem_image rPG _).mp (QRegister.image_compose_subset rPG _ hm_t) with ⟨i, hi⟩
    exact hdisj_SP.ne _ i hi.symm
  have hcin_C : wCin0 ∉ rGid.image := fun hm_c ↦ by
    rcases (QRegister.mem_image rWork _).mp (QRegister.image_compose_subset rWork _ hm_c) with ⟨k,
        hk⟩
    exact hdisj_SW.ne _ k hk.symm
  (DynamicCircuit.circuit c_xor_fwd).seq
    ((symWrapDynList v out.steps
      ((DynamicCircuit.circuit (tDagList tWires)).seq
        ((gidneyApexInvDyn v (4 - s) uWires rMidPG rGid wCin0
            hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C).seq
          (DynamicCircuit.circuit Circuit.identity)))).seq
      (DynamicCircuit.circuit c_xor_inv))
theorem xorForestBatch_spec {kSys mWork : ℕ} (v : Var) (s : ℕ) (cfg : ForestSlotConfig s)
    (L : ℕ) (hs : s ≤ 3) (hL : 1 ≤ L) (hm : xorForestBatchWork s cfg L ≤ mWork)
    (rSys : QRegister kSys n) (rPG : QRegister 7 n) (rWork : QRegister mWork n)
    (hdisj_SP : rSys.DisjointWires rPG) (hdisj_SW : rSys.DisjointWires rWork)
    (hdisj_PW : rPG.DisjointWires rWork) (idxAx : Fin L → Fin 6 → Fin kSys) (hinj_ax :
    Function.Injective (fun p : Fin L × Fin 6 ↦ idxAx p.1 p.2)) : (xorForestBatchFwdDyn v s
    cfg L hs hL hm rSys rPG rWork hdisj_SP hdisj_SW hdisj_PW idxAx hinj_ax).count TOFF = 0 ∧
    (xorForestBatchFwdDyn v s cfg L hs hL hm rSys rPG rWork hdisj_SP hdisj_SW hdisj_PW idxAx
    hinj_ax).count .T = xorForestBatchTCost s cfg L ∧ (xorForestBatchInvDyn v s cfg L hs hL hm
    rSys rPG rWork hdisj_SP hdisj_SW hdisj_PW idxAx hinj_ax).count TOFF = 0 ∧
    (xorForestBatchInvDyn v s cfg L hs hL hm rSys rPG rWork hdisj_SP hdisj_SW hdisj_PW idxAx
    hinj_ax).count .T = xorForestBatchTCost s cfg L ∧ (∀ [Fintype Var] [DecidableEq Var], ∃ (Φ
    : BitAssignment kSys → ℤ) (uLow : BitAssignment kSys → ℕ), (∀ γ : BitAssignment kSys, Φ γ
    + ((2 ^ s * uLow γ : ℕ) : ℤ) = ∑ l : Fin L, (forestAxisNat s cfg (fun i ↦ γ (idxAx l i)) :
    ℤ)) ∧ RealizesEmbeddedUnitaryWithCleanWorkspace (rSys.concat rPG hdisj_SP) rWork
    (apexCatUnitary kSys s hs Φ uLow) (xorForestBatchFwdDyn v s cfg L hs hL hm rSys rPG rWork
    hdisj_SP hdisj_SW hdisj_PW idxAx hinj_ax) ∧ RealizesEmbeddedUnitaryWithCleanWorkspace
    (rSys.concat rPG hdisj_SP) rWork (apexCatUnitary kSys s hs Φ uLow)⁻¹ (xorForestBatchInvDyn
    v s cfg L hs hL hm rSys rPG rWork hdisj_SP hdisj_SW hdisj_PW idxAx hinj_ax)) := by
  let wpairs := batchCnotPairs rSys cfg.pairs idxAx
  have hne_fwd : ∀ wp ∈ wpairs, wp.1 ≠ wp.2 := batchCnotPairs_hne rSys cfg.pairs cfg.hne idxAx
      hinj_ax
  have hne_inv : ∀ wp ∈ wpairs.reverse, wp.1 ≠ wp.2 := fun wp hwp ↦ hne_fwd wp (List.mem_reverse.mp
      hwp)
  have hwp_sys : ∀ wp ∈ wpairs, wp.1 ∈ rSys.image ∧ wp.2 ∈ rSys.image :=
    batchCnotPairs_mem_sys rSys cfg.pairs idxAx
  let c_xor_fwd : Circuit n := cnotPairsCircuit wpairs hne_fwd
  let c_xor_inv : Circuit n := cnotPairsCircuit wpairs.reverse hne_inv
  let col0Bucket : List (Wire n) :=
    finMapList (fun i : Fin (L - 1) ↦ rSys (idxAx ⟨i.val + 1, by omega⟩ cfg.qCin0)) ++
      expandColWires rSys idxAx cfg.col0Tail6
  let colRest : Fin (3 - s) → List (Wire n) :=
    fun r ↦ expandColWires rSys idxAx (cfg.colRest6 r)
  let buckets : List (List (Wire n)) := col0Bucket :: finMapList colRest
  have hmap_len : buckets.map List.length = xorForestBucketsLen s cfg L := by
    simp only [buckets, xorForestBucketsLen, List.map_cons, col0Bucket, List.length_append,
      finMapList_length, finMapList_map_length_eq_ofFn, expandColWires_length, colRest]
  have hsteps_eq : compressStepsCount buckets 0 = compressStepsNat (xorForestBucketsLen s cfg L) 0
      := by
    rw [compressStepsCount_eq_nat, hmap_len]
  have hfit_csa : 0 + compressStepsCount buckets 0 ≤ mWork := by
    dsimp only [xorForestBatchWork] at hm; rw [hsteps_eq]; omega
  have hB_nodup : ∀ B ∈ buckets, B.Nodup := fun B hB ↦ by
    rcases List.mem_cons.mp hB with rfl | hB_rest
    · rw [List.nodup_append]
      refine ⟨finMapList_nodup (fun i₁ i₂ h ↦ by
          have hp : ((⟨i₁.val + 1, by omega⟩, cfg.qCin0) : Fin L × Fin 6) =
              (⟨i₂.val + 1, by omega⟩, cfg.qCin0) := hinj_ax (rSys.wires.injective h)
          have hv : i₁.val + 1 = i₂.val + 1 := congrArg (fun p : Fin L × Fin 6 ↦ p.1.val) hp
          exact Fin.ext (by omega)),
        expandColWires_nodup rSys idxAx hinj_ax cfg.col0Tail6 cfg.hTailNodup,
        fun x hx y hy hxy ↦ ?_⟩
      subst hxy
      rcases mem_finMapList.mp hx with ⟨i, rfl⟩
      rcases (mem_expandColWires rSys idxAx cfg.col0Tail6 _).mp hy with ⟨q', hq', l, heq⟩
      have hp : ((l, q') : Fin L × Fin 6) = (⟨i.val + 1, by omega⟩, cfg.qCin0) :=
        hinj_ax (rSys.wires.injective heq)
      have hq_eq : q' = cfg.qCin0 := congrArg Prod.snd hp
      exact cfg.hCinNotTail (hq_eq ▸ hq')
    · rcases mem_finMapList.mp hB_rest with ⟨r, rfl⟩
      exact expandColWires_nodup rSys idxAx hinj_ax (cfg.colRest6 r) (cfg.hRestNodup r)
  have hB_disj : buckets.Pairwise fun B₁ B₂ ↦ ∀ x ∈ B₁, x ∉ B₂ := by
    rw [List.pairwise_cons]
    refine ⟨fun B₂ hB₂ x hx₁ hx₂ ↦ ?_,
      buckets_pairwise_finMapList colRest fun r₁ r₂ hne x hx₁ hx₂ ↦ ?_⟩
    · rcases mem_finMapList.mp hB₂ with ⟨r, rfl⟩
      rcases (mem_expandColWires rSys idxAx (cfg.colRest6 r) x).mp hx₂ with ⟨q₂, hq₂, l₂, rfl⟩
      rcases List.mem_append.mp hx₁ with hx_cin | hx_tail
      · rcases mem_finMapList.mp hx_cin with ⟨i, heq⟩
        have hp : ((⟨i.val + 1, by omega⟩, cfg.qCin0) : Fin L × Fin 6) = (l₂, q₂) :=
          hinj_ax (rSys.wires.injective heq)
        have hq_eq : q₂ = cfg.qCin0 := (congrArg Prod.snd hp).symm
        exact cfg.hCinDisjRest r (hq_eq ▸ hq₂)
      · rcases (mem_expandColWires rSys idxAx cfg.col0Tail6 _).mp hx_tail with ⟨q₁, hq₁, l₁, heq⟩
        have hp : ((l₁, q₁) : Fin L × Fin 6) = (l₂, q₂) := hinj_ax (rSys.wires.injective heq)
        have hq_eq : q₂ = q₁ := (congrArg Prod.snd hp).symm
        exact cfg.hTailDisjRest r q₁ hq₁ (hq_eq ▸ hq₂)
    · rcases (mem_expandColWires rSys idxAx (cfg.colRest6 r₁) x).mp hx₁ with ⟨q₁, hq₁, l₁, rfl⟩
      rcases (mem_expandColWires rSys idxAx (cfg.colRest6 r₂) _).mp hx₂ with ⟨q₂, hq₂, l₂, heq⟩
      have hp : ((l₂, q₂) : Fin L × Fin 6) = (l₁, q₁) := hinj_ax (rSys.wires.injective heq)
      have hq_eq : q₂ = q₁ := congrArg Prod.snd hp
      exact cfg.hRestDisj r₁ r₂ hne q₁ hq₁ (hq_eq ▸ hq₂)
  have hB_sys : ∀ B ∈ buckets, ∀ x ∈ B, x ∈ rSys.image := fun B hB x hx ↦ by
    rcases List.mem_cons.mp hB with rfl | hB_rest
    · rcases List.mem_append.mp hx with hx_cin | hx_tail
      · rcases mem_finMapList.mp hx_cin with ⟨_, rfl⟩
        exact (QRegister.mem_image rSys _).mpr ⟨_, rfl⟩
      · rcases (mem_expandColWires rSys idxAx cfg.col0Tail6 x).mp hx_tail with ⟨_, _, _, rfl⟩
        exact (QRegister.mem_image rSys _).mpr ⟨_, rfl⟩
    · rcases mem_finMapList.mp hB_rest with ⟨r, rfl⟩
      rcases (mem_expandColWires rSys idxAx (cfg.colRest6 r) x).mp hx with ⟨_, _, _, rfl⟩
      exact (QRegister.mem_image rSys _).mpr ⟨_, rfl⟩
  have hB_anc : ∀ B ∈ buckets, ∀ x ∈ B, x ∉ rWork.image := fun B hB x hx hm_w ↦ by
    rcases (QRegister.mem_image rSys x).mp (hB_sys B hB x hx) with ⟨i, rfl⟩
    rcases (QRegister.mem_image rWork _).mp hm_w with ⟨k, hk⟩
    exact hdisj_SW.ne i k hk.symm
  have hB_PG : ∀ B ∈ buckets, ∀ x ∈ B, x ∉ rPG.image := fun B hB x hx hm_pg ↦ by
    rcases (QRegister.mem_image rSys x).mp (hB_sys B hB x hx) with ⟨i, rfl⟩
    rcases (QRegister.mem_image rPG _).mp hm_pg with ⟨k, hk⟩
    exact hdisj_SP.ne i k hk.symm
  let out := compressBuckets rWork buckets 0 hfit_csa hB_nodup hB_disj hB_anc
  have hspec := compressBuckets_spec rPG.image rWork
    (disjWires_image (QRegExt.disjointWires_symm hdisj_PW)) buckets 0 hfit_csa hB_nodup hB_disj
      hB_anc hB_PG
  have hst : out.steps.length = compressStepsNat (xorForestBucketsLen s cfg L) 0 :=
    hspec.2.1.trans hsteps_eq
  have hcar_len : out.carries.length = finalCarriesNat (xorForestBucketsLen s cfg L) 0 := by
    rw [compressBuckets_carries_length, hmap_len]
  refine ⟨by
      unfold xorForestBatchFwdDyn
      simp only [count_dyn_seq, count_dyn_circuit, count_cnotPairsCircuit_toff,
        count_symWrapDynList_toff, count_tList_toff, count_gidneyApexChainDyn_toff,
        count_cir_id],
    by
      unfold xorForestBatchFwdDyn xorForestBatchTCost
      simp only[count_dyn_seq, count_dyn_circuit, count_cnotPairsCircuit_t,
          count_symWrapDynList_t, count_tList_t, count_gidneyApexChainDyn_t, count_cir_id]
      rw [hst, hcar_len]; omega,
    by
      unfold xorForestBatchInvDyn
      simp only [count_dyn_seq, count_dyn_circuit, count_cnotPairsCircuit_toff,
        count_symWrapDynList_toff, count_tDagList_toff, count_gidneyApexInvDyn_toff,
        count_cir_id],
    by
      unfold xorForestBatchInvDyn xorForestBatchTCost
      simp only[count_dyn_seq, count_dyn_circuit, count_cnotPairsCircuit_t,
          count_symWrapDynList_t, count_tDagList_t, count_gidneyApexInvDyn_t, count_cir_id]
      rw [hst, hcar_len]; omega,
    ?_⟩
  intro _ _
  let st := out.steps.length
  have hm' : 1 + st + (4 - s) ≤ mWork := by dsimp only [xorForestBatchWork] at hm; omega
  let rGid : QRegister (4 - s) n := rWork.slice (0 + st) (4 - s) (by omega)
  let wZero : Wire n := rWork ⟨st + (4 - s), by omega⟩
  have hblen : buckets.length = 4 - s := by
    simp only [buckets, List.length_cons, finMapList_length]; omega
  have hsw_len : out.sumWires.length = 4 - s := hspec.1.trans hblen
  let wCin0 : Wire n := rSys (idxAx ⟨0, hL⟩ cfg.qCin0)
  let tWires : List (Wire n) := out.carries
  let rMidPG : QRegister (4 - s) n := rPG.slice s (4 - s) (by omega)
  let uWires : Fin (4 - s) → Wire n := fun j ↦
    optWireOrZero wZero (out.sumWires.get ⟨j.val, by omega⟩)
  have hu_T : ∀ j, uWires j ∉ rMidPG.image := fun j hm_t ↦ by
    have hm_pg : uWires j ∈ rPG.image := QRegister.image_compose_subset rPG _ hm_t
    dsimp only [uWires] at hm_pg
    cases hget : out.sumWires.get ⟨j.val, by omega⟩ with
    | none =>
        rw [hget] at hm_pg; dsimp only [optWireOrZero, wZero] at hm_pg
        rcases (QRegister.mem_image rPG _).mp hm_pg with ⟨i, hi⟩
        exact hdisj_PW.ne i ⟨st + (4 - s), by omega⟩ hi
    | some w =>
        rw [hget] at hm_pg; dsimp only [optWireOrZero] at hm_pg
        rcases hspec.2.2.2.2.1 _ (List.get_mem _ _) w hget with ⟨B, hB, hwB⟩ | ⟨k, hk, _, _, rfl⟩
        · exact hB_PG B hB w hwB hm_pg
        · rcases (QRegister.mem_image rPG _).mp hm_pg with ⟨i, hi⟩
          exact hdisj_PW.ne i ⟨k, hk⟩ hi
  have hu_C : ∀ j, uWires j ∉ rGid.image := fun j hm_c ↦ by
    rcases (QRegister.mem_image rGid _).mp hm_c with ⟨i, hi⟩
    have hi' : rGid i = rWork ⟨st + i.val, by omega⟩ := by
      rw [QRegister.slice_apply]; exact congrArg rWork (Fin.ext (by simp))
    rw [hi'] at hi
    dsimp only [uWires] at hi
    cases hget : out.sumWires.get ⟨j.val, by omega⟩ with
    | none =>
        rw [hget] at hi; dsimp only [optWireOrZero, wZero] at hi
        have hv := congrArg Fin.val (rWork.wires.injective hi); dsimp at hv; omega
    | some w =>
        rw [hget] at hi; dsimp only [optWireOrZero] at hi
        rcases hspec.2.2.2.2.1 _ (List.get_mem _ _) w hget with ⟨B, hB, hwB⟩ | ⟨k, hk, _, hk_lt,
            rfl⟩
        · exact hB_anc B hB w hwB ((QRegister.mem_image rWork _).mpr ⟨_, hi⟩)
        · have hv := congrArg Fin.val (rWork.wires.injective hi)
          dsimp at hv; have := hspec.2.1; omega
  have hdisj_TC : rMidPG.DisjointWires rGid := (hdisj_PW.compose_left _).compose_right _
  have hwcin_not_B : ∀ B ∈ buckets, wCin0 ∉ B := fun B hB hmem ↦ by
    rcases List.mem_cons.mp hB with rfl | hB_rest
    · rcases List.mem_append.mp hmem with hcin | htail
      · rcases mem_finMapList.mp hcin with ⟨i, heq⟩
        have hp : ((⟨i.val + 1, by omega⟩, cfg.qCin0) : Fin L × Fin 6) = (⟨0, hL⟩, cfg.qCin0) :=
          hinj_ax (rSys.wires.injective heq)
        have hv : i.val + 1 = 0 := congrArg (fun p : Fin L × Fin 6 ↦ p.1.val) hp
        omega
      · rcases (mem_expandColWires rSys idxAx cfg.col0Tail6 _).mp htail with ⟨q', hq', l, heq⟩
        have hp : ((l, q') : Fin L × Fin 6) = (⟨0, hL⟩, cfg.qCin0) :=
          hinj_ax (rSys.wires.injective heq)
        have hq_eq : q' = cfg.qCin0 := congrArg Prod.snd hp
        exact cfg.hCinNotTail (hq_eq ▸ hq')
    · rcases mem_finMapList.mp hB_rest with ⟨r, rfl⟩
      rcases (mem_expandColWires rSys idxAx (cfg.colRest6 r) _).mp hmem with ⟨q', hq', l, heq⟩
      have hp : ((l, q') : Fin L × Fin 6) = (⟨0, hL⟩, cfg.qCin0) :=
        hinj_ax (rSys.wires.injective heq)
      have hq_eq : q' = cfg.qCin0 := congrArg Prod.snd hp
      exact cfg.hCinDisjRest r (hq_eq ▸ hq')
  have hcin_u : ∀ j, wCin0 ≠ uWires j := fun j heq ↦ by
    dsimp only [uWires] at heq
    cases hget : out.sumWires.get ⟨j.val, by omega⟩ with
    | none =>
        rw [hget] at heq; dsimp only [optWireOrZero, wZero, wCin0] at heq
        exact hdisj_SW.ne _ ⟨st + (4 - s), by omega⟩ heq
    | some w =>
        rw [hget] at heq; dsimp only [optWireOrZero] at heq
        rcases hspec.2.2.2.2.1 _ (List.get_mem _ _) w hget with ⟨B, hB, hwB⟩ | ⟨k, hk, _, _, rfl⟩
        · rw [← heq] at hwB
          exact hwcin_not_B B hB hwB
        · exact hdisj_SW.ne _ ⟨k, hk⟩ heq
  have hcin_T : wCin0 ∉ rMidPG.image := fun hm_t ↦ by
    rcases (QRegister.mem_image rPG _).mp (QRegister.image_compose_subset rPG _ hm_t) with ⟨i, hi⟩
    exact hdisj_SP.ne _ i hi.symm
  have hcin_C : wCin0 ∉ rGid.image := fun hm_c ↦ by
    rcases (QRegister.mem_image rWork _).mp (QRegister.image_compose_subset rWork _ hm_c) with ⟨k,
        hk⟩
    exact hdisj_SW.ne _ k hk.symm
  let f_xor_fwd : BitAssignment n → BitAssignment n := cnotPairsPerm wpairs
  let f_xor_inv : BitAssignment n → BitAssignment n := cnotPairsPerm wpairs.reverse
  let β₂_of : BitAssignment kSys → BitAssignment n :=
    fun γ ↦ symStepFwdList out.steps (f_xor_fwd (canonAssign rSys γ))
  let Φ : BitAssignment kSys → ℤ := fun γ ↦ 16 * (wireListSum tWires (β₂_of γ) : ℤ)
  let uLow : BitAssignment kSys → ℕ :=
    fun γ ↦ weightedOptWiresVal out.sumWires (β₂_of γ) + (β₂_of γ wCin0).val
  have hU_steps : ∀ s' ∈ out.steps, s'.S ⊆ rSys.image ∪ rWork.image := fun s' hs' w hw ↦ by
    rcases hspec.2.2.2.2.2.2.1 s' hs' w hw with ⟨B, hB, hwB⟩ | ⟨k, hk, _, _, rfl⟩
    · exact Finset.mem_union_left _ (hB_sys B hB w hwB)
    · exact Finset.mem_union_right _ ((QRegister.mem_image rWork _).mpr ⟨⟨k, hk⟩, rfl⟩)
  have hcin0_unchanged : ∀ δ : BitAssignment n, symStepFwdList out.steps δ wCin0 = δ wCin0 :=
    fun δ ↦ symStepFwdList_outside out.steps δ wCin0 fun s' hs' hm_s ↦ by
      rcases hspec.2.2.2.2.2.2.1 s' hs' _ hm_s with ⟨B, hB, hwB⟩ | ⟨k, hk, _, _, heq⟩
      · exact hwcin_not_B B hB hwB
      · exact hdisj_SW.ne _ ⟨k, hk⟩ heq
  have hxor_fwd_outside_sys : ∀ (δ : BitAssignment n) (w : Wire n), w ∉ rSys.image → f_xor_fwd
      δ w = δ w := fun δ w hw ↦ cnotPairsPerm_outside wpairs δ w fun wp hwp heq ↦ hw
      (heq ▸ (hwp_sys wp hwp).2)
  have hxor_inv_outside_sys : ∀ (δ : BitAssignment n) (w : Wire n), w ∉ rSys.image → f_xor_inv
      δ w = δ w := fun δ w hw ↦ cnotPairsPerm_outside wpairs.reverse δ w fun wp hwp heq ↦ hw
      (heq ▸ (hwp_sys wp (List.mem_reverse.mp hwp)).2)
  have hag_U : ∀ (β : BitAssignment n), (∀ j : Fin mWork, β (rWork j) = 0) →
      ∀ w ∈ rSys.image ∪ rWork.image,
        symStepFwdList out.steps (f_xor_fwd β) w = β₂_of (fun i ↦ β (rSys i)) w := by
    intro β hzero
    let γ : BitAssignment kSys := fun i ↦ β (rSys i)
    refine symStepFwdList_eq_on_superset out.steps hU_steps ?_
    refine cnotPairsPerm_eq_on_superset wpairs (fun wp hwp ↦ ⟨Finset.mem_union_left _ (hwp_sys
      wp hwp).1, Finset.mem_union_left _ (hwp_sys wp hwp).2⟩) fun w hw ↦ ?_
    rcases Finset.mem_union.mp hw with hws | hww
    · rcases (QRegister.mem_image rSys w).mp hws with ⟨i, rfl⟩
      exact (canonAssign_apply_sys rSys γ i).symm
    · have hnot_sys : w ∉ rSys.image := fun hm_s ↦ by
        rcases (QRegister.mem_image rSys w).mp hm_s with ⟨i, rfl⟩
        rcases (QRegister.mem_image rWork _).mp hww with ⟨j, hj⟩
        exact hdisj_SW.ne i j hj.symm
      rw [canonAssign_apply_outside rSys γ hnot_sys]
      rcases (QRegister.mem_image rWork w).mp hww with ⟨j, rfl⟩
      exact hzero j
  have hsum_Φ_uLow : ∀ γ : BitAssignment kSys, Φ γ + ((2 ^ s * uLow γ : ℕ) : ℤ) = ∑ l : Fin L,
      (forestAxisNat s cfg (fun i ↦ γ (idxAx l i)) : ℤ) := by
    intro γ
    let β₁ := f_xor_fwd (canonAssign rSys γ)
    have hzero_canon : ∀ k, 0 ≤ k → (hk : k < mWork) → β₁ (rWork ⟨k, hk⟩) = 0 := fun k _ hk ↦ by
      have hnot_sys : rWork ⟨k, hk⟩ ∉ rSys.image := fun hm_s ↦ by
        rcases (QRegister.mem_image rSys _).mp hm_s with ⟨i, hi⟩
        exact hdisj_SW.ne i ⟨k, hk⟩ hi
      dsimp only [β₁]
      rw [hxor_fwd_outside_sys _ _ hnot_sys, canonAssign_apply_outside rSys γ hnot_sys]
    have hcons := hspec.2.2.2.2.2.2.2 β₁ hzero_canon
    rw [hblen] at hcons
    have hscale_csa : 2 ^ s * weightedOptWiresVal out.sumWires (β₂_of γ) +
        16 * wireListSum out.carries (β₂_of γ) = 2 ^ s * weightedBucketsVal buckets β₁ := by
      have hp4 : 2 ^ s * 2 ^ (4 - s) = 16 := two_pow_mul_four_sub s hs
      calc 2 ^ s * weightedOptWiresVal out.sumWires (β₂_of γ) +
            16 * wireListSum out.carries (β₂_of γ)
          = 2 ^ s * (weightedOptWiresVal out.sumWires (β₂_of γ) +
              2 ^ (4 - s) * wireListSum out.carries (β₂_of γ)) := by
              rw [mul_add, ← mul_assoc, hp4]
        _ = 2 ^ s * weightedBucketsVal buckets β₁ := congrArg (2 ^ s * ·) hcons
    have hcin0_eq : (β₂_of γ wCin0).val = (β₁ wCin0).val :=
      congrArg ZMod.val (hcin0_unchanged β₁)
    have hnat_eq : 16 * wireListSum tWires (β₂_of γ) + 2 ^ s * uLow γ =
        ∑ l : Fin L, forestAxisNat s cfg (fun i ↦ γ (idxAx l i)) := by
      dsimp only [tWires, uLow]
      calc 16 * wireListSum out.carries (β₂_of γ) +
            2 ^ s * (weightedOptWiresVal out.sumWires (β₂_of γ) + (β₂_of γ wCin0).val)
          = 2 ^ s * (β₂_of γ wCin0).val +
            (2 ^ s * weightedOptWiresVal out.sumWires (β₂_of γ) +
              16 * wireListSum out.carries (β₂_of γ)) := by ring
        _ = 2 ^ s * ((β₁ wCin0).val + weightedBucketsVal buckets β₁) := by
              rw [hcin0_eq, hscale_csa]; ring
        _ = ∑ l : Fin L, forestAxisNat s cfg (fun i ↦ γ (idxAx l i)) :=
              weightedBuckets_forest_eq s cfg hL rSys idxAx hinj_ax γ
    dsimp only [Φ]
    calc (16 * (wireListSum tWires (β₂_of γ) : ℤ)) + ((2 ^ s * uLow γ : ℕ) : ℤ)
        = ((16 * wireListSum tWires (β₂_of γ) + 2 ^ s * uLow γ : ℕ) : ℤ) := by push_cast; ring
      _ = ∑ l : Fin L, (forestAxisNat s cfg (fun i ↦ γ (idxAx l i)) : ℤ) := by
          rw [hnat_eq]; push_cast; rfl
  have hhc_xor_fwd : PhasePerm rSys.image c_xor_fwd (fun _ ↦ 1) f_xor_fwd :=
    PhasePerm.of_classicalPerm (classicalPerm_cnotPairsCircuit wpairs hne_fwd) hxor_fwd_outside_sys
  have hhc_xor_inv : PhasePerm rSys.image c_xor_inv (fun _ ↦ 1) f_xor_inv :=
    PhasePerm.of_classicalPerm (classicalPerm_cnotPairsCircuit wpairs.reverse hne_inv)
        hxor_inv_outside_sys
  have hcancel_xor : ∀ (f_m : BitAssignment n → BitAssignment n),
      (∀ δ w, w ∉ rPG.image → f_m δ w = δ w) →
      ∀ β w, w ∉ rPG.image → f_xor_inv (f_m (f_xor_fwd β)) w = β w := by
    intro f_m hout_m β w hw
    let S_nonPG : Finset (Wire n) := Finset.univ \ rPG.image
    have hmem_S : ∀ u : Wire n, u ∈ S_nonPG ↔ u ∉ rPG.image := by simp [S_nonPG]
    have hsys_S : ∀ u ∈ rSys.image, u ∈ S_nonPG := fun u hu ↦
      (hmem_S u).mpr fun hpg ↦ by
        rcases (QRegister.mem_image rSys u).mp hu with ⟨i, rfl⟩
        rcases (QRegister.mem_image rPG _).mp hpg with ⟨j, hj⟩
        exact hdisj_SP.ne i j hj.symm
    have heq_inv := cnotPairsPerm_eq_on_superset (S := S_nonPG) wpairs.reverse
      (fun wp hwp ↦ by
        have hs := hwp_sys wp (List.mem_reverse.mp hwp)
        exact ⟨hsys_S _ hs.1, hsys_S _ hs.2⟩)
      (β₁ := f_m (f_xor_fwd β)) (β₂ := f_xor_fwd β)
      (fun u hu ↦ hout_m (f_xor_fwd β) u ((hmem_S u).mp hu))
      w ((hmem_S w).mpr hw)
    dsimp only [f_xor_inv, f_xor_fwd] at heq_inv ⊢
    rw [heq_inv, cnotPairsPerm_reverse_cancel wpairs hne_fwd β]
  have hpg_not_sys : ∀ j : Fin 7, rPG j ∉ rSys.image := fun j hm_s ↦ by
    rcases (QRegister.mem_image rSys _).mp hm_s with ⟨i, hi⟩
    exact hdisj_SP.ne i j hi
  have hpg_xor_eq : ∀ (f_m : BitAssignment n → BitAssignment n) (β : BitAssignment n),
      regVal rPG (f_xor_inv (f_m (f_xor_fwd β))) = regVal rPG (f_m (f_xor_fwd β)) :=
    fun f_m β ↦ regVal_congr rPG fun j ↦ hxor_inv_outside_sys _ (rPG j) (hpg_not_sys j)
  have hpg_in_eq : ∀ (β : BitAssignment n) (j : Fin 7),
      symStepFwdList out.steps (f_xor_fwd β) (rPG j) = β (rPG j) := fun β j ↦ by
    rw [symStepFwdList_outside out.steps (f_xor_fwd β) (rPG j) (fun s' hs' hm_s ↦ by
      rcases hspec.2.2.2.2.2.2.1 s' hs' _ hm_s with ⟨B, hB, hwB⟩ | ⟨k, hk, _, _, heq⟩
      · exact hB_PG B hB _ hwB ((QRegister.mem_image rPG _).mpr ⟨j, rfl⟩)
      · exact hdisj_PW.ne j ⟨k, hk⟩ heq)]
    exact hxor_fwd_outside_sys β (rPG j) (hpg_not_sys j)
  have hpg_reg_in : ∀ β : BitAssignment n, regVal rPG (symStepFwdList out.steps (f_xor_fwd β))
      = regVal rPG β := fun β ↦ regVal_congr rPG (hpg_in_eq β)
  have hmid_reg_in : ∀ β : BitAssignment n,
      regVal rMidPG (symStepFwdList out.steps (f_xor_fwd β)) =
        ((regVal rPG β) / 2 ^ s) % 2 ^ (4 - s) := fun β ↦ by
    rw [regVal_midSlice7_eq s hs rPG _, hpg_reg_in β]
  have hwork_not_sys : ∀ k : Fin mWork, rWork k ∉ rSys.image := fun k hm_s ↦ by
    rcases (QRegister.mem_image rSys _).mp hm_s with ⟨i, hi⟩
    exact hdisj_SW.ne i k hi
  have hgid_zero_β₂ : ∀ β : BitAssignment n, (∀ j : Fin mWork, β (rWork j) = 0) →
      ∀ i : Fin (4 - s), symStepFwdList out.steps (f_xor_fwd β) (rGid i) = 0 := by
    intro β hzero i
    have hi' : rGid i = rWork ⟨st + i.val, by omega⟩ := by
      rw [QRegister.slice_apply]; exact congrArg rWork (Fin.ext (by simp))
    rw [hi', symStepFwdList_outside out.steps (f_xor_fwd β) _ (fun s' hs' hm_s ↦ by
      rcases hspec.2.2.2.2.2.2.1 s' hs' _ hm_s with ⟨B, hB, hwB⟩ | ⟨k, hk, _, hk_lt, heq⟩
      · exact hB_anc B hB _ hwB ((QRegister.mem_image rWork _).mpr ⟨_, rfl⟩)
      · have hv := congrArg Fin.val (rWork.wires.injective heq)
        dsimp at hv; have := hspec.2.1; omega)]
    rw [hxor_fwd_outside_sys β _ (hwork_not_sys ⟨st + i.val, by omega⟩)]
    exact hzero ⟨st + i.val, by omega⟩
  have huLow_on_β : ∀ β : BitAssignment n, (∀ j : Fin mWork, β (rWork j) = 0) → bitsVal
      (fun j ↦ symStepFwdList out.steps (f_xor_fwd β) (uWires j)) +
      (symStepFwdList out.steps (f_xor_fwd β) wCin0).val = uLow (fun i ↦ β (rSys i)) := by
    intro β hzero
    let γ : BitAssignment kSys := fun i ↦ β (rSys i)
    let δ := symStepFwdList out.steps (f_xor_fwd β)
    have hag := hag_U β hzero
    have hz_δ : δ wZero = 0 := by
      dsimp only [δ]
      rw [hag wZero (Finset.mem_union_right _ ((QRegister.mem_image rWork _).mpr ⟨_, rfl⟩))]
      dsimp only [β₂_of]
      rw [symStepFwdList_outside out.steps _ wZero (fun s' hs' hm_s ↦ by
          rcases hspec.2.2.2.2.2.2.1 s' hs' _ hm_s with ⟨B, hB, hwB⟩ | ⟨k, hk, _, hk_lt, heq⟩
          · exact hB_anc B hB _ hwB ((QRegister.mem_image rWork _).mpr ⟨_, rfl⟩)
          · have hv := congrArg Fin.val (rWork.wires.injective heq)
            dsimp [wZero] at hv; have := hspec.2.1; omega),
        hxor_fwd_outside_sys _ _ (hwork_not_sys ⟨st + (4 - s), by omega⟩),
        canonAssign_apply_outside rSys γ (hwork_not_sys ⟨st + (4 - s), by omega⟩)]
    have hbv := weightedOptWiresVal_eq_bitsVal wZero out.sumWires hsw_len δ hz_δ
    dsimp only [uWires]
    rw [hbv]
    have hsw_eq_u : weightedOptWiresVal out.sumWires δ =
        weightedOptWiresVal out.sumWires (β₂_of γ) :=
      weightedOptWiresVal_congr fun ow how w hsome ↦
        hag w (by
          rcases hspec.2.2.2.2.1 ow how w hsome with ⟨B, hB, hwB⟩ | ⟨k, hk, _, _, rfl⟩
          · exact Finset.mem_union_left _ (hB_sys B hB w hwB)
          · exact Finset.mem_union_right _ ((QRegister.mem_image rWork _).mpr ⟨⟨k, hk⟩, rfl⟩))
    have hcin_u_eq : δ wCin0 = β₂_of γ wCin0 :=
      hag wCin0 (Finset.mem_union_left _ ((QRegister.mem_image rSys _).mpr ⟨_, rfl⟩))
    change weightedOptWiresVal out.sumWires δ + (δ wCin0).val = uLow γ
    rw [hsw_eq_u, hcin_u_eq]
  have htWires_on_β : ∀ β : BitAssignment n, (∀ j : Fin mWork, β (rWork j) = 0) →
      wireListSum tWires (symStepFwdList out.steps (f_xor_fwd β)) =
        wireListSum tWires (β₂_of (fun i ↦ β (rSys i))) := by
    intro β hzero
    refine wireListSum_congr fun w hw ↦ hag_U β hzero w ?_
    rcases hspec.2.2.2.1 w hw with ⟨k, hk, _, rfl⟩
    exact Finset.mem_union_right _ ((QRegister.mem_image rWork _).mpr ⟨⟨k, hk⟩, rfl⟩)
  have hMid_sub_PG : rMidPG.image ⊆ rPG.image := QRegister.image_compose_subset rPG _
  refine ⟨Φ, uLow, hsum_Φ_uLow, ?_, ?_⟩
  · obtain ⟨φ_add, f_add, hp_add0, hval_add, hwp_add⟩ := gidneyApexChain_correct v false
      (4 - s) uWires rMidPG rGid wCin0 hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C
    have hp_add : PhasePerm rPG.image _ φ_add f_add := hp_add0.mono hMid_sub_PG
    have hcpp_gid : CleanPhasePerm rGid rPG.image (gidneyApexChainDyn v false (4 - s) uWires
        rMidPG rGid wCin0 hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C) (gidneyApexChainCircuit
        false (4 - s) uWires rMidPG rGid wCin0 hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C) φ_add
        f_add := ⟨hp_add, fun Q ↦ gidneyApexChainDyn_wp_const v false (4 - s) uWires rMidPG
        rGid wCin0 hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C Q, fun Q ↦ hwp_add _ fun _ _ ↦ rfl⟩
    have hcpp_in0 := cleanPhasePerm_sandwich_phase
      (tList tWires) Circuit.identity _ (fun _ ↦ 1) id id
      (phasePerm_tList tWires) (PhasePerm.identity ∅) (Finset.disjoint_empty_left _) hcpp_gid
    have hcpp_in : CleanPhasePerm rGid rPG.image
        ((DynamicCircuit.circuit (tList tWires)).seq
          ((gidneyApexChainDyn v false (4 - s) uWires rMidPG rGid wCin0
              hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C).seq
            (DynamicCircuit.circuit Circuit.identity)))
        (tList tWires ;;ᶜ
          gidneyApexChainCircuit false (4 - s) uWires rMidPG rGid wCin0
            hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C ;;ᶜ
          Circuit.identity)
        _ f_add :=
      CleanPhasePerm.mono_work_and_set hcpp_in0 (Finset.Subset.refl _) (by simp)
    have ⟨f_mid, hp_mid, hM_mid, hwp_mid⟩ := symWrapDynList_phasePerm_correct v rPG.image
        rWork 0 (4 - s) out.steps hspec.2.2.2.2.2.1 (by omega) _ _ _ _ hcpp_in.phasePerm
        (restrictAssertionToZeroAncilla_sandwich_var v rGid ∅ (tList tWires) Circuit.identity
        _ id (phasePerm_tList tWires) (Finset.disjoint_empty_left _) _ _ hwp_add)
    have hcpp_mid : CleanPhasePerm rWork rPG.image (symWrapDynList v out.steps
        ((DynamicCircuit.circuit (tList tWires)).seq ((gidneyApexChainDyn v false (4 - s)
        uWires rMidPG rGid wCin0 hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C).seq
        (DynamicCircuit.circuit Circuit.identity)))) (symWrapCircuitList out.steps _) _ f_mid
        := CleanPhasePerm.mono_work_and_set ⟨hp_mid, fun Q ↦ symWrapDynList_wp_const v
        out.steps _ hcpp_in.wp_const Q, fun Q ↦ hwp_mid _ fun _ _ ↦ rfl⟩
        (QRegister.image_compose_subset rWork _) (Finset.Subset.refl _)
    have hcpp_tot := cleanPhasePerm_sandwich_phase c_xor_fwd c_xor_inv (fun _ ↦ 1) (fun _ ↦ 1)
      f_xor_fwd f_xor_inv hhc_xor_fwd hhc_xor_inv (disjWires_image hdisj_SW) hcpp_mid
    refine cleanPhasePerm_realizes_genCatPhasePerm hdisj_SP hcpp_tot
      (fun γ ↦ midSlicePerm7 s hs (uLow γ)) (fun γ m ↦ Φ γ + 16 * (((((m.val / 2 ^ s) % 2 ^ (4
      - s)) + uLow γ) / 2 ^ (4 - s) : ℕ) : ℤ)) (fun β hzero ↦ ?_)
      (fun β q hq ↦ hcancel_xor f_mid hp_mid.outside β q hq) (fun β hzero ↦ ?_)
    · let δ := symStepFwdList out.steps (f_xor_fwd β)
      obtain ⟨hφ_a, _⟩ := hval_add δ (hgid_zero_β₂ β hzero)
      dsimp only [id, Φ]
      simp only [one_mul, mul_one]
      change dyadicTurn 7 (16 * (wireListSum tWires δ : ℤ)) * φ_add δ = _
      rw [htWires_on_β β hzero, hφ_a, dyadicTurn_add]
      congr 1
      have hS_eq : regVal rMidPG δ + bitsVal (fun j ↦ δ (uWires j)) + (δ wCin0).val =
          ((regVal rPG β) / 2 ^ s) % 2 ^ (4 - s) + uLow (fun i ↦ β (rSys i)) := by
        rw [hmid_reg_in β, add_assoc, huLow_on_β β hzero]
      rw [hS_eq]
      simp
    · let δ := symStepFwdList out.steps (f_xor_fwd β)
      obtain ⟨_, hreg_a⟩ := hval_add δ (hgid_zero_β₂ β hzero)
      dsimp only [Function.comp_apply]
      rw [hpg_xor_eq f_mid β]
      have hreg_m : regVal rPG (f_mid (f_xor_fwd β)) = regVal rPG (f_add δ) :=
        regVal_congr rPG fun j ↦ hM_mid (f_xor_fwd β) (rPG j) ((QRegister.mem_image rPG _).mpr ⟨j,
            rfl⟩)
      rw [hreg_m, regVal_after_midSlice7 s hs rPG f_add δ (hp_add0.outside δ),
        hpg_reg_in β, hreg_a, hmid_reg_in β, add_assoc, huLow_on_β β hzero]
      rfl
  · rw [apexCatUnitary, genCatPhasePermUnitary_inv]
    obtain ⟨φ_sub, f_sub, hcpp_sub0, hval_sub, hwp_sub⟩ := gidneyApexInv_correct v (4 - s)
        uWires rMidPG rGid wCin0 hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C
    have hcpp_gid : CleanPhasePerm rGid rPG.image (gidneyApexInvDyn v (4 - s) uWires rMidPG
        rGid wCin0 hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C) (gidneyApexInvCircuit (4 - s)
        uWires rMidPG rGid wCin0 hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C) φ_sub f_sub :=
        CleanPhasePerm.mono_work_and_set hcpp_sub0 (Finset.Subset.refl _) hMid_sub_PG
    have hcpp_in0 := cleanPhasePerm_sandwich_phase
      (tDagList tWires) Circuit.identity _ (fun _ ↦ 1) id id
      (phasePerm_tDagList tWires) (PhasePerm.identity ∅) (Finset.disjoint_empty_left _) hcpp_gid
    have hcpp_in : CleanPhasePerm rGid rPG.image
        ((DynamicCircuit.circuit (tDagList tWires)).seq
          ((gidneyApexInvDyn v (4 - s) uWires rMidPG rGid wCin0
              hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C).seq
            (DynamicCircuit.circuit Circuit.identity)))
        (tDagList tWires ;;ᶜ
          gidneyApexInvCircuit (4 - s) uWires rMidPG rGid wCin0
            hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C ;;ᶜ
          Circuit.identity)
        _ f_sub :=
      CleanPhasePerm.mono_work_and_set hcpp_in0 (Finset.Subset.refl _) (by simp)
    have ⟨f_mid, hp_mid, hM_mid, hwp_mid⟩ := symWrapDynList_phasePerm_correct
      v rPG.image rWork 0 (4 - s) out.steps hspec.2.2.2.2.2.1 (by omega)
      _ _ _ _ hcpp_in.phasePerm
      (restrictAssertionToZeroAncilla_sandwich_var v rGid ∅ (tDagList tWires) Circuit.identity
        _ id (phasePerm_tDagList tWires) (Finset.disjoint_empty_left _) _ _ hwp_sub)
    have hcpp_mid : CleanPhasePerm rWork rPG.image (symWrapDynList v out.steps
        ((DynamicCircuit.circuit (tDagList tWires)).seq ((gidneyApexInvDyn v (4 - s) uWires
        rMidPG rGid wCin0 hu_T hu_C hdisj_TC hcin_u hcin_T hcin_C).seq (DynamicCircuit.circuit
        Circuit.identity)))) (symWrapCircuitList out.steps _) _ f_mid :=
        CleanPhasePerm.mono_work_and_set ⟨hp_mid, fun Q ↦ symWrapDynList_wp_const v out.steps
        _ hcpp_in.wp_const Q, fun Q ↦ hwp_mid _ fun _ _ ↦ rfl⟩
        (QRegister.image_compose_subset rWork _) (Finset.Subset.refl _)
    have hcpp_tot := cleanPhasePerm_sandwich_phase c_xor_fwd c_xor_inv (fun _ ↦ 1) (fun _ ↦ 1)
      f_xor_fwd f_xor_inv hhc_xor_fwd hhc_xor_inv (disjWires_image hdisj_SW) hcpp_mid
    refine cleanPhasePerm_realizes_genCatPhasePerm hdisj_SP hcpp_tot
      (fun γ ↦ (midSlicePerm7 s hs (uLow γ)).symm) (fun γ k ↦ -(Φ γ + 16 *
      (((((((midSlicePerm7 s hs (uLow γ)).symm k).val / 2 ^ s) % 2 ^ (4 - s)) + uLow γ) / 2 ^
      (4 - s) : ℕ) : ℤ))) (fun β hzero ↦ ?_)
      (fun β q hq ↦ hcancel_xor f_mid hp_mid.outside β q hq) (fun β hzero ↦ ?_)
    · let γ : BitAssignment kSys := fun i ↦ β (rSys i)
      let δ := symStepFwdList out.steps (f_xor_fwd β)
      let k : Fin (2 ^ 7) := ⟨regVal rPG β, regVal_lt_two_pow rPG β⟩
      let W := 2 ^ (4 - s)
      have hW : 0 < W := by positivity
      let m' := (midSlicePerm7 s hs (uLow γ)).symm k
      have hek : midSlicePerm7 s hs (uLow γ) m' = k :=
        (midSlicePerm7 s hs (uLow γ)).apply_symm_apply k
      have hm'_mid_lt : (m'.val / 2 ^ s) % W < W := Nat.mod_lt _ hW
      have hk_mid : ((m'.val / 2 ^ s) % W + uLow γ) % W = (k.val / 2 ^ s) % W := by
        have hlo : m'.val % 2 ^ s < 2 ^ s := Nat.mod_lt _ (by positivity)
        have hmid : ((m'.val / 2 ^ s) % W + uLow γ) % W < W := Nat.mod_lt _ hW
        have hhi : m'.val / 16 < 8 := by have := m'.isLt; omega
        have hp2 := (pack7Slices_parts s hs _ _ _ hlo hmid hhi).2.1
        have hval_eq : pack7Slices s (m'.val % 2 ^ s) (((m'.val / 2 ^ s) % W + uLow γ) % W)
            (m'.val / 16) = k.val := congrArg Fin.val hek
        rw [hval_eq] at hp2
        exact hp2.symm
      have hdiv_eq : ((W - 1 - ((k.val / 2 ^ s) % W)) + uLow γ) / W =
          (((m'.val / 2 ^ s) % W) + uLow γ) / W := by
        rw [← hk_mid]
        exact ones_complement_div_eq W ((m'.val / 2 ^ s) % W) (uLow γ) hW hm'_mid_lt
      obtain ⟨hφ_s, _⟩ := hval_sub δ (hgid_zero_β₂ β hzero)
      dsimp only [id, Φ]
      simp only [one_mul, mul_one]
      change dyadicTurn 7 (-16 * (wireListSum tWires δ : ℤ)) * φ_sub δ = _
      rw [htWires_on_β β hzero, hφ_s, dyadicTurn_add]
      congr 1
      have hS_inv : (W - 1 - regVal rMidPG δ) + bitsVal (fun j ↦ δ (uWires j)) + (δ wCin0).val
          = (W - 1 - ((k.val / 2 ^ s) % W)) + uLow γ := by
        rw [hmid_reg_in β, add_assoc, huLow_on_β β hzero]
      change -16 * (wireListSum tWires (β₂_of γ) : ℤ) + (-16 : ℤ) * (((((W - 1 - regVal rMidPG
        δ) + bitsVal (fun j ↦ δ (uWires j)) + (δ wCin0).val) / W : ℕ) : ℤ)) = -(16 *
        (wireListSum tWires (β₂_of γ) : ℤ) + 16 * (((((m'.val / 2 ^ s) % W + uLow γ) / W : ℕ)
        : ℤ)))
      rw [hS_inv, hdiv_eq]
      ring
    · let δ := symStepFwdList out.steps (f_xor_fwd β)
      obtain ⟨_, hreg_s⟩ := hval_sub δ (hgid_zero_β₂ β hzero)
      dsimp only [Function.comp_apply]
      rw [hpg_xor_eq f_mid β]
      have hreg_m : regVal rPG (f_mid (f_xor_fwd β)) = regVal rPG (f_sub δ) :=
        regVal_congr rPG fun j ↦ hM_mid (f_xor_fwd β) (rPG j) ((QRegister.mem_image rPG _).mpr ⟨j,
            rfl⟩)
      rw [hreg_m, regVal_after_midSlice7 s hs rPG f_sub δ (hcpp_sub0.phasePerm.outside δ),
        hpg_reg_in β, hreg_s, hmid_reg_in β, add_assoc, huLow_on_β β hzero]
      rfl
attribute [irreducible] xorForestBatchFwdDyn xorForestBatchInvDyn
end ApexButterflyEngine128
def idxForestAx (off L : ℕ) (_hoff : off + L ≤ 654) (l : Fin L) (q : Fin 6) :
    Fin (3924 + 3) :=
  ⟨6 * (off + l.val) + q.val, by omega⟩
theorem idxForestAx_inj (off L : ℕ) (hoff : off + L ≤ 654) :
    Function.Injective (fun p : Fin L × Fin 6 ↦ idxForestAx off L hoff p.1 p.2) := by
  intro ⟨l₁, q₁⟩ ⟨l₂, q₂⟩ h
  have hv := congrArg Fin.val h
  dsimp only [idxForestAx] at hv
  have hl : l₁.val = l₂.val := by have := q₁.isLt; have := q₂.isLt; omega
  have hq : q₁.val = q₂.val := by omega
  exact Prod.ext (Fin.ext hl) (Fin.ext hq)
def forestTermAxis (φ6 : Fin 64 → ℤ) (γ : BitAssignment (3924 + 3)) (a : ℕ) : ℤ :=
  if ha : a < 654 then
    φ6 ((basisBitsEquiv 6).symm fun q : Fin 6 ↦ γ ⟨6 * a + q.val, by omega⟩)
  else 0
def xorForestBatchFwdDyn128 (s off L : ℕ) (cfg : ForestSlotConfig s) (hs : s ≤ 3) (hL : 1 ≤ L)
    (hoff : off + L ≤ 654) (hwMax : xorForestBatchWork s cfg L ≤ 128) : DynamicCircuit Unit
    nCanon4062 := xorForestBatchFwdDyn () s cfg L hs hL (le_refl (xorForestBatchWork s cfg L))
    rSysCanon128 rPGCanon128 (rWorkCanon128.slice 0 (xorForestBatchWork s cfg L) (Nat.zero_add
    _ ▸ hwMax)) rSysCanon128_disjoint_rPGCanon128
    (rSysCanon128_disjoint_rWorkCanon128.compose_right _)
    (rPGCanon128_disjoint_rWorkCanon128.compose_right _) (idxForestAx off L hoff)
    (idxForestAx_inj off L hoff)
def xorForestBatchInvDyn128 (s off L : ℕ) (cfg : ForestSlotConfig s) (hs : s ≤ 3) (hL : 1 ≤ L)
    (hoff : off + L ≤ 654) (hwMax : xorForestBatchWork s cfg L ≤ 128) : DynamicCircuit Unit
    nCanon4062 := xorForestBatchInvDyn () s cfg L hs hL (le_refl (xorForestBatchWork s cfg L))
    rSysCanon128 rPGCanon128 (rWorkCanon128.slice 0 (xorForestBatchWork s cfg L) (Nat.zero_add
    _ ▸ hwMax)) rSysCanon128_disjoint_rPGCanon128
    (rSysCanon128_disjoint_rWorkCanon128.compose_right _)
    (rPGCanon128_disjoint_rWorkCanon128.compose_right _) (idxForestAx off L hoff)
    (idxForestAx_inj off L hoff)
theorem xorForestBatch128_exists (s off L : ℕ) (cfg : ForestSlotConfig s) (φ6 : Fin 64 → ℤ)
    (hφ6 : ∀ u : Fin 64, (forestAxisNat s cfg (basisBits 6 u) : ℤ) = φ6 u) (hs : s ≤ 3)
    (hL : 1 ≤ L) (hoff : off + L ≤ 654) (hwMax : xorForestBatchWork s cfg L ≤ 128) : ∃ uCat :
    Unitary (2 ^ (3924 + 3 + 7)), (xorForestBatchFwdDyn128 s off L cfg hs hL hoff hwMax).count
    TOFF = 0 ∧ (xorForestBatchInvDyn128 s off L cfg hs hL hoff hwMax).count TOFF = 0 ∧
    (xorForestBatchFwdDyn128 s off L cfg hs hL hoff hwMax).count .T = xorForestBatchTCost s
    cfg L ∧ (xorForestBatchInvDyn128 s off L cfg hs hL hoff hwMax).count .T =
    xorForestBatchTCost s cfg L ∧ RealizesEmbeddedUnitaryWithCleanWorkspace rQftCanon128
    rWorkCanon128 uCat (xorForestBatchFwdDyn128 s off L cfg hs hL hoff hwMax) ∧
    RealizesEmbeddedUnitaryWithCleanWorkspace rQftCanon128 rWorkCanon128 uCat⁻¹
    (xorForestBatchInvDyn128 s off L cfg hs hL hoff hwMax) ∧ (∀ {N : ℕ} [NeZero (2 ^ N)] (rId
    : QRegister (3924 + 3) N) (rPG : QRegister 7 N) (hdisj : rId.DisjointWires rPG) (U_cat7 :
    Unitary (2 ^ 7)), U_cat7.1.mulVec (Pi.single 0 1) = DyadicQft64.phaseGradKet 7 →
    DyadicQft64.IntertwinesCatOp (rPG.embedUnitary U_cat7).1 (rPG.basisOutcomeProjector 0)
    ((rId.concat rPG hdisj).embedUnitary uCat).1 (rId.embedUnitary
    (DyadicQft64.dyadicDiagUnitary (3924 + 3) 7 (fun γ ↦ ∑ r : Fin L, forestTermAxis φ6 γ (off
    + r.val)))).1) := by
  obtain ⟨hToffF, hTF, hToffI, hTI, hRest⟩ := xorForestBatch_spec () s cfg L hs hL
      (le_refl (xorForestBatchWork s cfg L)) rSysCanon128 rPGCanon128 (rWorkCanon128.slice 0
      (xorForestBatchWork s cfg L) (Nat.zero_add _ ▸ hwMax)) rSysCanon128_disjoint_rPGCanon128
      (rSysCanon128_disjoint_rWorkCanon128.compose_right _)
      (rPGCanon128_disjoint_rWorkCanon128.compose_right _) (idxForestAx off L hoff)
      (idxForestAx_inj off L hoff)
  obtain ⟨Φ, uLow, hEqExp, hRF, hRI⟩ := hRest
  refine ⟨apexCatUnitary (3924 + 3) s hs Φ uLow, hToffF, hToffI, hTF, hTI,
    realizes_congr_slice (Nat.zero_add _ ▸ hwMax) (rIdOfCat_concat_rPGOfCat rQftCanon128) hRF,
    realizes_congr_slice (Nat.zero_add _ ▸ hwMax) (rIdOfCat_concat_rPGOfCat rQftCanon128) hRI, ?_⟩
  intro N _ rId rPG hdisj U_cat7 hcol0
  have heff : DyadicQft64.dyadicDiagUnitary (3924 + 3) 7
      (fun γ ↦ Φ γ + ((2 ^ s * uLow γ : ℕ) : ℤ)) = DyadicQft64.dyadicDiagUnitary (3924 + 3) 7
      (fun γ ↦ ∑ r : Fin L, forestTermAxis φ6 γ (off + r.val)) := by
    congr 1; funext γ
    rw [hEqExp γ]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    have ha : off + r.val < 654 := by have := r.isLt; omega
    let b6 : Fin 6 → ZMod 2 := fun q ↦ γ ⟨6 * (off + r.val) + q.val, by omega⟩
    let u6 : Fin 64 := (basisBitsEquiv 6).symm b6
    have hb_eq : b6 = basisBits 6 u6 := ((basisBitsEquiv 6).apply_symm_apply b6).symm
    simp only [forestTermAxis, ha, ↓reduceDIte, idxForestAx]
    change (forestAxisNat s cfg b6 : ℤ) = φ6 u6
    rw [hb_eq]
    exact hφ6 u6
  rw [← heff]
  exact apexCatUnitary_intertwinesCat s hs rId rPG hdisj U_cat7 hcol0 Φ uLow
/-- `CanonStageSpec128` constructor for an `L`-axis Hadamard-Forest CSA+Gidney batch. -/
noncomputable def xorForestBatchCanonStage128 (s off L tB : ℕ) (cfg : ForestSlotConfig s)
    (φ6 : Fin 64 → ℤ) (hφ6 : ∀ u : Fin 64, (forestAxisNat s cfg (basisBits 6 u) : ℤ) = φ6 u)
    (hs : s ≤ 3) (hL : 1 ≤ L) (hoff : off + L ≤ 654)
    (hwMax : xorForestBatchWork s cfg L ≤ 128)
    (htB : xorForestBatchTCost s cfg L = tB) : CanonStageSpec128 where
  uCat := Classical.choose (xorForestBatch128_exists s off L cfg φ6 hφ6 hs hL hoff hwMax)
  uEff := DyadicQft64.dyadicDiagUnitary (3924 + 3) 7
    (fun γ ↦ ∑ r : Fin L, forestTermAxis φ6 γ (off + r.val))
  tCost := tB
  dFwd := xorForestBatchFwdDyn128 s off L cfg hs hL hoff hwMax
  dInv := xorForestBatchInvDyn128 s off L cfg hs hL hoff hwMax
  hToffFwd := (Classical.choose_spec (xorForestBatch128_exists s off L cfg φ6 hφ6 hs hL hoff
      hwMax)).1
  hToffInv := (Classical.choose_spec (xorForestBatch128_exists s off L cfg φ6 hφ6 hs hL hoff
      hwMax)).2.1
  hTFwd := (Classical.choose_spec (xorForestBatch128_exists s off L cfg φ6 hφ6 hs hL hoff
      hwMax)).2.2.1.trans htB
  hTInv := (Classical.choose_spec (xorForestBatch128_exists s off L cfg φ6 hφ6 hs hL hoff
      hwMax)).2.2.2.1.trans htB
  hRealFwd := (Classical.choose_spec (xorForestBatch128_exists s off L cfg φ6 hφ6 hs hL hoff
      hwMax)).2.2.2.2.1
  hRealInv := (Classical.choose_spec (xorForestBatch128_exists s off L cfg φ6 hφ6 hs hL hoff
      hwMax)).2.2.2.2.2.1
  hIntertwines := (Classical.choose_spec (xorForestBatch128_exists s off L cfg φ6 hφ6 hs hL hoff
      hwMax)).2.2.2.2.2.2
noncomputable def diag6Unitary (φ : Fin 64 → ℤ) : Unitary 64 :=
  ⟨Matrix.diagonal fun u : Fin 64 ↦ omega128 (φ u), by
    rw [Matrix.mem_unitaryGroup_iff']
    change (Matrix.diagonal _)ᴴ * Matrix.diagonal _ = 1
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext u
    exact star_mul_omega128_self _⟩
def w16Ctrl (k : Fin 5) : Fin 6 := ⟨k.val + 1, by omega⟩
def w16Tgt (k : Fin 5) : Fin 6 := ⟨k.val, by omega⟩
theorem w16Ctrl_ne_tgt (k : Fin 5) : w16Ctrl k ≠ w16Tgt k := by
  fin_cases k <;> decide
def w16AxisCircuit (k : Fin 5) : Circuit 6 :=
    (Circuit.CNOT (w16Ctrl k) (w16Tgt k) (w16Ctrl_ne_tgt k)).seq ((Circuit.T (w16Tgt k)).seq
    (Circuit.CNOT (w16Ctrl k) (w16Tgt k) (w16Ctrl_ne_tgt k)))
def w16Exp6 (k : Fin 5) (u : Fin 64) : ℤ :=
  16 * (bitXor (bit6 u (w16Ctrl k)) (bit6 u (w16Tgt k)) : ℤ)
theorem w16AxisCircuit_eval (k : Fin 5) :
    (w16AxisCircuit k).eval = diag6Unitary (w16Exp6 k) := by
  apply Subtype.ext
  apply phasePerm_to_diagonal6 (w16AxisCircuit k)
  let m : Fin 6 := w16Ctrl k
  let t : Fin 6 := w16Tgt k
  have hne : m ≠ t := w16Ctrl_ne_tgt k
  let fc : BitAssignment 6 → BitAssignment 6 := fun γ ↦ Function.update γ t (γ t + γ m)
  have hcnot : PhasePerm ({t} : Finset (Wire 6)) (Circuit.CNOT m t hne) (fun _ ↦ 1) fc :=
    PhasePerm.of_classicalPerm (ClassicalPerm.CNOT m t hne) (fun γ w hw ↦ by
      have hwt : w ≠ t := by simpa using hw
      exact Function.update_of_ne hwt _ _)
  have htail := ((PhasePerm.gateT t).mono (Finset.empty_subset _)).seq hcnot
  have hfull := hcnot.seq htail
  have hperm_id : ((fc ∘ id) ∘ fc) = (id : BitAssignment 6 → BitAssignment 6) := by
    funext β w
    dsimp only [Function.comp_apply, id_eq, fc]
    by_cases hwt : w = t
    · subst hwt
      rw [Function.update_self, Function.update_of_ne hne, Function.update_self,
        zmod2_add_cancel_right]
    · rw [Function.update_of_ne hwt, Function.update_of_ne hwt]
  have hp0 : PhasePerm (∅ : Finset (Wire 6)) (w16AxisCircuit k)
      (fun β ↦ 1 * (dyadicTurn 7 (16 * (fc β t).val) * 1)) id := by
    refine { evolve := fun β ↦ ?_, outside := fun _ _ _ ↦ rfl }
    have hev := hfull.evolve β
    rw [hperm_id] at hev
    exact hev
  refine PhasePerm.congr_phase hp0 fun β ↦ ?_
  simp only [one_mul, mul_one]
  congr 1
  have hxor : ∀ a b : ZMod 2, ((b + a).val : ℤ) = (bitXor a.val b.val : ℤ) := by decide
  dsimp only [fc, w16Exp6, m, t]
  rw [Function.update_self, hxor (β (w16Ctrl k)) (β (w16Tgt k)),
    bit6_basisBitsEquiv_symm, bit6_basisBitsEquiv_symm]
/-- `L`-axis weight-16 stage on `CanonStageSpec128` (`L` `T` gates, `TOFF = 0`). -/
noncomputable def stageW16PrefixCanonStage128 (L : ℕ) (hL : L ≤ 654) (k : Fin 5) :
    CanonStageSpec128 :=
  (CanonStageSpec128.ofAxisPrefixCircuit L hL (w16AxisCircuit k) (diag6Unitary (w16Exp6 k)) 1
    (by fin_cases k <;> decide)
    (by fin_cases k <;> decide)
    (by fin_cases k <;> decide)
    (by fin_cases k <;> decide)
    (w16AxisCircuit_eval k)).congr
    (uEff' := axisProdPrefix L hL (fun _ ↦ diag6Unitary (w16Exp6 k)))
    (tCost' := L) rfl (Nat.mul_one L)
def forestCfg3 : ForestSlotConfig 3 where
  pairs := [(5, 3)]
  hne := by decide
  qCin0 := 3
  col0Tail6 := []
  colRest6 := Fin.elim0
  hCinNotTail := by decide
  hTailNodup := by decide
  hRestNodup := fun r ↦ Fin.elim0 r
  hCinDisjRest := fun r ↦ Fin.elim0 r
  hTailDisjRest := fun r ↦ Fin.elim0 r
  hRestDisj := fun r ↦ Fin.elim0 r
def forestExp3 (u : Fin 64) : ℤ := 8 * (bitXor (bit6 u 5) (bit6 u 3) : ℤ)
theorem forestCfg3_exp_eq : ∀ u : Fin 64, (forestAxisNat 3 forestCfg3 (basisBits 6 u) : ℤ) =
    forestExp3 u := by
  decide
def forestCfg2 : ForestSlotConfig 2 where
  pairs := [(4, 1), (2, 4), (5, 2)]
  hne := by decide
  qCin0 := 1
  col0Tail6 := [2]
  colRest6 := fun _ ↦ [4]
  hCinNotTail := by decide
  hTailNodup := by decide
  hRestNodup := by decide
  hCinDisjRest := by decide
  hTailDisjRest := by decide
  hRestDisj := by decide
def forestExp2 (u : Fin 64) : ℤ := 4 * (bitXor (bit6 u 4) (bit6 u 1) : ℤ) + 4 *
    (bitXor (bit6 u 5) (bit6 u 2) : ℤ) + 8 * (bitXor (bit6 u 4) (bit6 u 2) : ℤ)
theorem forestCfg2_exp_eq : ∀ u : Fin 64, (forestAxisNat 2 forestCfg2 (basisBits 6 u) : ℤ) =
    forestExp2 u := by
  decide
def forestCfg1 : ForestSlotConfig 1 where
  pairs := [(0, 4), (3, 0), (1, 3), (5, 1)]
  hne := by decide
  qCin0 := 4
  col0Tail6 := [1]
  colRest6 := ![([0] : List (Fin 6)), [3]]
  hCinNotTail := by decide
  hTailNodup := by decide
  hRestNodup := by decide
  hCinDisjRest := by decide
  hTailDisjRest := by decide
  hRestDisj := by decide
def forestExp1 (u : Fin 64) : ℤ := 2 * (bitXor (bit6 u 4) (bit6 u 0) : ℤ) + 2 *
    (bitXor (bit6 u 5) (bit6 u 1) : ℤ) + 4 * (bitXor (bit6 u 3) (bit6 u 0) : ℤ) + 8 *
    (bitXor (bit6 u 3) (bit6 u 1) : ℤ)
theorem forestCfg1_exp_eq : ∀ u : Fin 64, (forestAxisNat 1 forestCfg1 (basisBits 6 u) : ℤ) =
    forestExp1 u := by
  decide
def forestCfg0 : ForestSlotConfig 0 where
  pairs := [(0, 5), (0, 2)]
  hne := by decide
  qCin0 := 5
  col0Tail6 := []
  colRest6 := fun r ↦ if r.val = 2 then [2] else []
  hCinNotTail := by decide
  hTailNodup := by decide
  hRestNodup := by decide
  hCinDisjRest := by decide
  hTailDisjRest := by decide
  hRestDisj := by decide
def forestExp0 (u : Fin 64) : ℤ := 1 * (bitXor (bit6 u 5) (bit6 u 0) : ℤ) + 8 *
    (bitXor (bit6 u 2) (bit6 u 0) : ℤ)
theorem forestCfg0_exp_eq : ∀ u : Fin 64, (forestAxisNat 0 forestCfg0 (basisBits 6 u) : ℤ) =
    forestExp0 u := by
  decide
/-- 1-electron (`L = 3` axes) Slot-3 Hadamard-Forest stage on `CanonStageSpec128` (`10 T`, `TOFF =
  0`). -/
noncomputable def activeOneElecSlot3Stage128 : CanonStageSpec128 :=
  xorForestBatchCanonStage128 3 0 3 10 forestCfg3 forestExp3 forestCfg3_exp_eq
    (by decide) (by decide) (by decide) (by decide) (by decide)
/-- 1-electron (`L = 3` axes) Slot-2 Hadamard-Forest stage on `CanonStageSpec128` (`27 T`, `TOFF =
  0`). -/
noncomputable def activeOneElecSlot2Stage128 : CanonStageSpec128 :=
  xorForestBatchCanonStage128 2 0 3 27 forestCfg2 forestExp2 forestCfg2_exp_eq
    (by decide) (by decide) (by decide) (by decide) (by decide)
/-- 1-electron (`L = 3` axes) Slot-1 Hadamard-Forest stage on `CanonStageSpec128` (`39 T`, `TOFF =
  0`). -/
noncomputable def activeOneElecSlot1Stage128 : CanonStageSpec128 :=
  xorForestBatchCanonStage128 1 0 3 39 forestCfg1 forestExp1 forestCfg1_exp_eq
    (by decide) (by decide) (by decide) (by decide) (by decide)
/-- 1-electron (`L = 3` axes) Slot-0 Hadamard-Forest stage on `CanonStageSpec128` (`26 T`, `TOFF =
  0`). -/
noncomputable def activeOneElecSlot0Stage128 : CanonStageSpec128 :=
  xorForestBatchCanonStage128 0 0 3 26 forestCfg0 forestExp0 forestCfg0_exp_eq
    (by decide) (by decide) (by decide) (by decide) (by decide)
theorem hL3_le_654 : 3 ≤ 654 := by decide
theorem axisProdPrefix_mul (L : ℕ) (hL : L ≤ 654) (f g : Fin L → Unitary 64) :
    axisProdPrefix L hL f * axisProdPrefix L hL g = axisProdPrefix L hL (fun a ↦ f a * g a) := by
  dsimp only [axisProdPrefix]
  exact prod_ofFn_embedUnitary_mul (rAxisPrefix L hL) (fun _ _ h ↦ rAxisPrefix_disjoint hL h) f g
theorem axisProdPrefix_diag6Unitary_eq_dyadicDiagUnitary (L : ℕ) (hL : L ≤ 654) (φ6 : Fin 64 → ℤ) :
    axisProdPrefix L hL (fun _ ↦ diag6Unitary φ6) =
      DyadicQft64.dyadicDiagUnitary (3924 + 3) 7
        (fun γ ↦ ∑ a : Fin L, forestTermAxis φ6 γ (0 + a.val)) := by
  apply Subtype.ext
  dsimp only [axisProdPrefix]
  have hmap_eq : ((List.ofFn fun a : Fin L ↦ (rAxisPrefix L hL a).embedUnitary (diag6Unitary
      φ6)).map Subtype.val) = (List.ofFn fun a : Fin L ↦ Matrix.diagonal fun x : Fin (2 ^
      (3924 + 3)) ↦ omega128 (φ6 ((rAxisPrefix L hL a).extractIndex x))) := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn; funext a
    rw [Function.comp_apply, QRegister.embedUnitary_val]
    exact PosMomSelectDynamic.embedMatrix_diagonal (rAxisPrefix L hL a) _
  rw [submonoid_coe_list_prod, hmap_eq, prod_ofFn_diagonal, DyadicQft64.dyadicDiagUnitary]
  apply congrArg Matrix.diagonal; funext x
  rw [prod_ofFn_omega128, ← DyadicQft64.dyadicTurn_eq_omega128]
  apply congrArg (DyadicQft64.dyadicTurn 7)
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  have ha : a.val < 654 := Nat.lt_of_lt_of_le a.isLt hL
  simp only [Nat.zero_add, forestTermAxis, ha, ↓reduceDIte]
  apply congrArg φ6
  apply (basisBitsEquiv 6).injective
  rw [(basisBitsEquiv 6).apply_symm_apply]
  funext q
  change basisBits 6 ((rAxisPrefix L hL a).extractIndex x) q = _
  rw [QRegister.basisBits_extractIndex]
  rfl
theorem diag6Unitary_mul_add (φ₁ φ₂ : Fin 64 → ℤ) :
    diag6Unitary φ₁ * diag6Unitary φ₂ = diag6Unitary (fun u ↦ φ₁ u + φ₂ u) := by
  apply Subtype.ext
  change Matrix.diagonal _ * Matrix.diagonal _ = Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1; funext u
  exact (omega128_add (φ₁ u) (φ₂ u)).symm
theorem stageDiag6_eq_diag6Unitary (m : Fin 6) :
    stageDiag6 m = diag6Unitary (stageRowExp128 m) := rfl
theorem wireHadamard6_comm_diag6 (m : Fin 6) (φ : Fin 64 → ℤ)
    (hindep : ∀ z w : Fin 64, (∀ r : Fin 6, r ≠ m → bit6 z r = bit6 w r) → φ z = φ w) :
    wireHadamard6 m * diag6Unitary φ = diag6Unitary φ * wireHadamard6 m := by
  apply Subtype.ext
  ext z w
  change ((wireHadamard6 m).1 * Matrix.diagonal (fun u ↦ omega128 (φ u))) z w =
    (Matrix.diagonal (fun u ↦ omega128 (φ u)) * (wireHadamard6 m).1) z w
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  let reg : QRegister 1 6 := QRegister.singleton m
  rw [wireHadamard6, QRegister.embedUnitary_val, reg.embedMatrix_apply]
  by_cases h : (reg.basisSplitEquiv z).2 = (reg.basisSplitEquiv w).2
  · have hOut := (reg.basisSplit_environment_eq_iff z w).mp h
    have hall : ∀ r : Fin 6, r ≠ m → bit6 z r = bit6 w r := fun r hr ↦ by
      have hnot : r ∉ Set.range reg.wires := by
        rintro ⟨idx, hidx⟩
        exact hr hidx.symm
      rw [bit6_eq_basisBits_val, bit6_eq_basisBits_val, hOut r hnot]
    rw [hindep z w hall, mul_comm]
  · simp [h]
def remExp4 (u : Fin 64) : ℤ := 8 * (bitXor (bit6 u 5) (bit6 u 3) : ℤ) + 4 *
    (bitXor (bit6 u 5) (bit6 u 2) : ℤ) + 2 * (bitXor (bit6 u 5) (bit6 u 1) : ℤ) + 1 *
    (bitXor (bit6 u 5) (bit6 u 0) : ℤ)
def remExp3 (u : Fin 64) : ℤ := 8 * (bitXor (bit6 u 4) (bit6 u 2) : ℤ) + 4 *
    (bitXor (bit6 u 4) (bit6 u 1) : ℤ) + 2 * (bitXor (bit6 u 4) (bit6 u 0) : ℤ) + 4 *
    (bitXor (bit6 u 5) (bit6 u 2) : ℤ) + 2 * (bitXor (bit6 u 5) (bit6 u 1) : ℤ) + 1 *
    (bitXor (bit6 u 5) (bit6 u 0) : ℤ)
def remExp2 (u : Fin 64) : ℤ := 8 * (bitXor (bit6 u 3) (bit6 u 1) : ℤ) + 4 *
    (bitXor (bit6 u 3) (bit6 u 0) : ℤ) + 2 * (bitXor (bit6 u 4) (bit6 u 0) : ℤ) + 2 *
    (bitXor (bit6 u 5) (bit6 u 1) : ℤ) + 1 * (bitXor (bit6 u 5) (bit6 u 0) : ℤ)
def remExp1 (u : Fin 64) : ℤ := 8 * (bitXor (bit6 u 2) (bit6 u 0) : ℤ) + 1 *
    (bitXor (bit6 u 5) (bit6 u 0) : ℤ)
theorem forest6_eq_orig6 :
    let h5 := wireHadamard6 5
    let h4 := wireHadamard6 4
    let h3 := wireHadamard6 3
    let h2 := wireHadamard6 2
    let h1 := wireHadamard6 1
    let h0 := wireHadamard6 0
    let s4 := diag6Unitary (w16Exp6 4)
    let s3 := diag6Unitary forestExp3 * diag6Unitary (w16Exp6 3)
    let s2 := diag6Unitary forestExp2 * diag6Unitary (w16Exp6 2)
    let s1 := diag6Unitary forestExp1 * diag6Unitary (w16Exp6 1)
    let s0 := diag6Unitary forestExp0 * diag6Unitary (w16Exp6 0)
    ((((h0 * (s0 * h1)) * (s1 * h2)) * (s2 * h3)) * (s3 * h4)) * (s4 * h5) =
      uCoreHadamard6 := by
  intro h5 h4 h3 h2 h1 h0 s4 s3 s2 s1 s0
  let r4 := diag6Unitary remExp4
  let r3 := diag6Unitary remExp3
  let r2 := diag6Unitary remExp2
  let r1 := diag6Unitary remExp1
  have hd5 : stageDiag6 5 = r4 * s4 := by
    dsimp only [r4, s4]; rw [stageDiag6_eq_diag6Unitary, diag6Unitary_mul_add]
    congr 1; funext u; revert u; decide
  have hc4 : h4 * r4 = r4 * h4 :=
    wireHadamard6_comm_diag6 4 remExp4 fun z w h ↦ by
      dsimp only [remExp4]
      rw [h 5 (by decide), h 3 (by decide), h 2 (by decide), h 1 (by decide), h 0 (by decide)]
  have hd4 : stageDiag6 4 * r4 = r3 * s3 := by
    dsimp only [r4, r3, s3]
    rw [stageDiag6_eq_diag6Unitary, diag6Unitary_mul_add, diag6Unitary_mul_add,
        diag6Unitary_mul_add]
    congr 1; funext u; revert u; decide
  have hc3 : h3 * r3 = r3 * h3 :=
    wireHadamard6_comm_diag6 3 remExp3 fun z w h ↦ by
      dsimp only [remExp3]
      rw [h 5 (by decide), h 4 (by decide), h 2 (by decide), h 1 (by decide), h 0 (by decide)]
  have hd3 : stageDiag6 3 * r3 = r2 * s2 := by
    dsimp only [r3, r2, s2]
    rw [stageDiag6_eq_diag6Unitary, diag6Unitary_mul_add, diag6Unitary_mul_add,
        diag6Unitary_mul_add]
    congr 1; funext u; revert u; decide
  have hc2 : h2 * r2 = r2 * h2 :=
    wireHadamard6_comm_diag6 2 remExp2 fun z w h ↦ by
      dsimp only [remExp2]
      rw [h 5 (by decide), h 4 (by decide), h 3 (by decide), h 1 (by decide), h 0 (by decide)]
  have hd2 : stageDiag6 2 * r2 = r1 * s1 := by
    dsimp only [r2, r1, s1]
    rw [stageDiag6_eq_diag6Unitary, diag6Unitary_mul_add, diag6Unitary_mul_add,
        diag6Unitary_mul_add]
    congr 1; funext u; revert u; decide
  have hc1 : h1 * r1 = r1 * h1 :=
    wireHadamard6_comm_diag6 1 remExp1 fun z w h ↦ by
      dsimp only [remExp1]
      rw [h 5 (by decide), h 2 (by decide), h 0 (by decide)]
  have hd1 : stageDiag6 1 * r1 = s0 := by
    dsimp only [r1, s0]
    rw [stageDiag6_eq_diag6Unitary, diag6Unitary_mul_add, diag6Unitary_mul_add]
    congr 1; funext u; revert u; decide
  unfold uCoreHadamard6
  symm
  calc ((((h0 * (stageDiag6 1 * h1)) * (stageDiag6 2 * h2)) *
          (stageDiag6 3 * h3)) * (stageDiag6 4 * h4)) * (stageDiag6 5 * h5)
      = h0 * stageDiag6 1 * h1 * stageDiag6 2 * h2 * stageDiag6 3 * h3 *
          stageDiag6 4 * (h4 * r4) * s4 * h5 := by
          rw [hd5]; simp only [_root_.mul_assoc]
    _ = h0 * stageDiag6 1 * h1 * stageDiag6 2 * h2 * stageDiag6 3 * h3 *
          (stageDiag6 4 * r4) * h4 * s4 * h5 := by
          rw [hc4]; simp only [_root_.mul_assoc]
    _ = h0 * stageDiag6 1 * h1 * stageDiag6 2 * h2 * stageDiag6 3 *
          (h3 * r3) * s3 * h4 * s4 * h5 := by
          rw [hd4]; simp only [_root_.mul_assoc]
    _ = h0 * stageDiag6 1 * h1 * stageDiag6 2 * h2 * (stageDiag6 3 * r3) *
          h3 * s3 * h4 * s4 * h5 := by
          rw [hc3]; simp only [_root_.mul_assoc]
    _ = h0 * stageDiag6 1 * h1 * stageDiag6 2 * (h2 * r2) * s2 *
          h3 * s3 * h4 * s4 * h5 := by
          rw [hd3]; simp only [_root_.mul_assoc]
    _ = h0 * stageDiag6 1 * h1 * (stageDiag6 2 * r2) * h2 * s2 *
          h3 * s3 * h4 * s4 * h5 := by
          rw [hc2]; simp only [_root_.mul_assoc]
    _ = h0 * stageDiag6 1 * (h1 * r1) * s1 * h2 * s2 *
          h3 * s3 * h4 * s4 * h5 := by
          rw [hd2]; simp only [_root_.mul_assoc]
    _ = h0 * (stageDiag6 1 * r1) * h1 * s1 * h2 * s2 *
          h3 * s3 * h4 * s4 * h5 := by
          rw [hc1]; simp only [_root_.mul_assoc]
    _ = ((((h0 * (s0 * h1)) * (s1 * h2)) * (s2 * h3)) * (s3 * h4)) * (s4 * h5) := by
          rw [hd1]; simp only [_root_.mul_assoc]
/-- Complete 6-stage Hadamard-Forest `QFT_64` `CanonStageSpec128` on the 1 active anchor electron
  (`L = 3` axes,
**`117 T` one-way = `234 T/step`**, `TOFF = 0`, saving **`-26 T/step`** below
`activeOneElecFullQftStage128`'s `130 T`). -/
noncomputable def rawActiveOneElecForestQftStage128 : CanonStageSpec128 :=
    (((stageHPrefixCanonStage128 3 hL3_le_654 5).seq (stageW16PrefixCanonStage128 3 hL3_le_654
    4)).seq (((stageHPrefixCanonStage128 3 hL3_le_654 4).seq ((stageW16PrefixCanonStage128 3
    hL3_le_654 3).seq activeOneElecSlot3Stage128)).seq (((stageHPrefixCanonStage128 3
    hL3_le_654 3).seq ((stageW16PrefixCanonStage128 3 hL3_le_654 2).seq
    activeOneElecSlot2Stage128)).seq (((stageHPrefixCanonStage128 3 hL3_le_654 2).seq
    ((stageW16PrefixCanonStage128 3 hL3_le_654 1).seq activeOneElecSlot1Stage128)).seq
    (((stageHPrefixCanonStage128 3 hL3_le_654 1).seq ((stageW16PrefixCanonStage128 3
    hL3_le_654 0).seq activeOneElecSlot0Stage128)).seq (stageHPrefixCanonStage128 3 hL3_le_654
    0))))))
theorem stage128_seq_uEff (A B : CanonStageSpec128) : (A.seq B).uEff = B.uEff * A.uEff := rfl
theorem stageHPrefix128_uEff (L : ℕ) (hL : L ≤ 654) (kf : Fin 6) :
    (stageHPrefixCanonStage128 L hL kf).uEff = axisProdPrefix L hL (fun _ ↦ wireHadamard6 kf) := rfl
theorem stageW16Prefix128_uEff (L : ℕ) (hL : L ≤ 654) (k : Fin 5) :
    (stageW16PrefixCanonStage128 L hL k).uEff = axisProdPrefix L hL (fun _ ↦ diag6Unitary (w16Exp6
        k)) := rfl
theorem activeOneElecSlot3_128_uEff :
    activeOneElecSlot3Stage128.uEff = axisProdPrefix 3 hL3_le_654 (fun _ ↦ diag6Unitary forestExp3)
        :=
  (axisProdPrefix_diag6Unitary_eq_dyadicDiagUnitary 3 hL3_le_654 forestExp3).symm
theorem activeOneElecSlot2_128_uEff :
    activeOneElecSlot2Stage128.uEff = axisProdPrefix 3 hL3_le_654 (fun _ ↦ diag6Unitary forestExp2)
        :=
  (axisProdPrefix_diag6Unitary_eq_dyadicDiagUnitary 3 hL3_le_654 forestExp2).symm
theorem activeOneElecSlot1_128_uEff :
    activeOneElecSlot1Stage128.uEff = axisProdPrefix 3 hL3_le_654 (fun _ ↦ diag6Unitary forestExp1)
        :=
  (axisProdPrefix_diag6Unitary_eq_dyadicDiagUnitary 3 hL3_le_654 forestExp1).symm
theorem activeOneElecSlot0_128_uEff :
    activeOneElecSlot0Stage128.uEff = axisProdPrefix 3 hL3_le_654 (fun _ ↦ diag6Unitary forestExp0)
        :=
  (axisProdPrefix_diag6Unitary_eq_dyadicDiagUnitary 3 hL3_le_654 forestExp0).symm
theorem rawActiveOneElecForestQftStage128_uEff_eq :
    rawActiveOneElecForestQftStage128.uEff = axisProdPrefix 3 hL3_le_654 (fun _ ↦ uCoreHadamard6)
        := by
  unfold rawActiveOneElecForestQftStage128
  simp only [stage128_seq_uEff, stageHPrefix128_uEff, stageW16Prefix128_uEff,
    activeOneElecSlot3_128_uEff, activeOneElecSlot2_128_uEff,
    activeOneElecSlot1_128_uEff, activeOneElecSlot0_128_uEff, axisProdPrefix_mul]
  exact congrArg (fun u6 ↦ axisProdPrefix 3 hL3_le_654 (fun _ ↦ u6)) forest6_eq_orig6
/-- Complete 6-stage `117-T` 1-electron Hadamard-Forest `QFT_64` `CanonStageSpec128` (`117 T`
  one-way = `234 T/step`, `TOFF = 0`). -/
noncomputable def activeOneElecForestFullQftStage128 : CanonStageSpec128 :=
  rawActiveOneElecForestQftStage128.congr
    (uEff' := axisProdPrefix 3 hL3_le_654 (fun _ ↦ uCoreHadamard6))
    (tCost' := 117)
    rawActiveOneElecForestQftStage128_uEff_eq
    rfl
@[simp] theorem activeOneElecForestFullQftStage128_tCost :
    activeOneElecForestFullQftStage128.tCost = 117 := rfl
/-- `k`-th binary bit (`k : Fin 7`) of a 7-bit momentum sum `s : Fin 128`. -/
def bit7 (s : Fin 128) (k : Fin 7) : ℕ := (s.val / 2 ^ k.val) % 2
/-- The 15 sub-32 Karatsuba XOR terms `∑_{1 ≤ m ≤ 5} ∑_{0 ≤ r < m} 2^{5 - m + r} * (bit6 z m ⊕ bit7
  s r)`
between the upper 5 bits `z_1..z_5` of `z : Fin 64` and the lower 5 bits `s_0..s_4` of `s : Fin
128`. -/
def pointCrossXorExp128 (z : Fin 64) (s : Fin 128) : ℤ := 1 *
    (bitXor (bit6 z 5) (bit7 s 0) : ℤ) + 2 * (bitXor (bit6 z 5) (bit7 s 1) : ℤ) + 2 *
    (bitXor (bit6 z 4) (bit7 s 0) : ℤ) + 4 * (bitXor (bit6 z 5) (bit7 s 2) : ℤ) + 4 *
    (bitXor (bit6 z 4) (bit7 s 1) : ℤ) + 4 * (bitXor (bit6 z 3) (bit7 s 0) : ℤ) + 8 *
    (bitXor (bit6 z 5) (bit7 s 3) : ℤ) + 8 * (bitXor (bit6 z 4) (bit7 s 2) : ℤ) + 8 *
    (bitXor (bit6 z 3) (bit7 s 1) : ℤ) + 8 * (bitXor (bit6 z 2) (bit7 s 0) : ℤ) + 16 *
    (bitXor (bit6 z 5) (bit7 s 4) : ℤ) + 16 * (bitXor (bit6 z 4) (bit7 s 3) : ℤ) + 16 *
    (bitXor (bit6 z 3) (bit7 s 2) : ℤ) + 16 * (bitXor (bit6 z 2) (bit7 s 1) : ℤ) + 16 *
    (bitXor (bit6 z 1) (bit7 s 0) : ℤ)
/-- `s`-independent target phase `∑_{j=0}^4 (2^j - 32) * bit6 z (5 - j)`. -/
def pointTargetOnlyExp128 (z : Fin 64) : ℤ := (-31) * (bit6 z 5 : ℤ) + (-30) * (bit6 z 4 : ℤ)
    + (-28) * (bit6 z 3 : ℤ) + (-24) * (bit6 z 2 : ℤ) + (-16) * (bit6 z 1 : ℤ)
/-- `0-T` Clifford phase (`S` on `s_1`, `S†` on `s_2..s_5`, `Z` on `s_6`, and 6 parallel `CZ` gates
  on `(z_r, s_r)`). -/
def pointSumCliffordExp128 (z : Fin 64) (s : Fin 128) : ℤ := 32 * (bit7 s 1 : ℤ) + 96 *
    ((bit7 s 2 : ℤ) + (bit7 s 3 : ℤ) + (bit7 s 4 : ℤ) + (bit7 s 5 : ℤ)) + 64 * (bit7 s 6 : ℤ)
    + 64 * ((bit6 z 5 : ℤ) * (bit7 s 5 : ℤ) + (bit6 z 4 : ℤ) * (bit7 s 4 : ℤ) + (bit6 z 3 : ℤ)
    * (bit7 s 3 : ℤ) + (bit6 z 2 : ℤ) * (bit7 s 2 : ℤ) + (bit6 z 1 : ℤ) * (bit7 s 1 : ℤ) +
    (bit6 z 0 : ℤ) * (bit7 s 0 : ℤ))
/-- `z`-independent `0-T` single-electron Clifford phase (`S†` on bit `1` and `S` on bits
  `2..5`). -/
def pointElecCliffordExp128 (u : Fin 64) : ℤ := 96 * (bit6 u 1 : ℤ) + 32 *
    ((bit6 u 2 : ℤ) + (bit6 u 3 : ℤ) + (bit6 u 4 : ℤ) + (bit6 u 5 : ℤ))
set_option maxHeartbeats 800000 in
-- `decide` over `Fin 64 × Fin 128` (`8,192` cases) exceeds default 200k heartbeats
/-- **Exact Mod-`128` Karatsuba-XOR Decomposition of `(31 - 2 * bitRev6 z) * s`**. -/
theorem pointLinearMul_emod_128_eq : ∀ (z : Fin 64) (s : Fin 128),
    ((31 - 2 * ((bitRev6 z).val : ℤ)) * (s.val : ℤ)) % 128 = (pointCrossXorExp128 z s +
    pointTargetOnlyExp128 z + pointSumCliffordExp128 z s) % 128 := by
  decide
theorem omega128_pointLinearMul_eq (z : Fin 64) (s : Fin 128) : omega128
    ((31 - 2 * ((bitRev6 z).val : ℤ)) * (s.val : ℤ)) = omega128 (pointCrossXorExp128 z s) *
    omega128 (pointTargetOnlyExp128 z) * omega128 (pointSumCliffordExp128 z s) := by
  rw [← omega128_add, ← omega128_add]
  exact omega128_eq_of_emod_eq (pointLinearMul_emod_128_eq z s)
theorem pointElecCliffordExp128_emod_128_eq : ∀ u : Fin 64,
    (32 * ∑ r : Fin 6, (1 - ((2 ^ r.val : ℕ) : ℤ)) * (bit6 u r : ℤ)) % 128 =
    pointElecCliffordExp128 u % 128 := by
  decide
theorem omega128_mul_int_emod_128 (c a : ℤ) :
    omega128 (c * a) = omega128 (c * (a % 128)) := by
  apply omega128_eq_of_emod_eq
  rw [Int.mul_emod c (a % 128) 128, Int.emod_emod, ← Int.mul_emod]
theorem omega128_sum_congr_emod {α : Type*} (S : Finset α) (f g : α → ℤ)
    (h : ∀ x ∈ S, f x % 128 = g x % 128) :
    omega128 (∑ x ∈ S, f x) = omega128 (∑ x ∈ S, g x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, omega128_add, omega128_add,
        omega128_eq_of_emod_eq (h a (Finset.mem_insert_self a s)),
        ih (fun x hx ↦ h x (Finset.mem_insert_of_mem hx))]
/-- **217-Electron `pointDiagUnitary6` Phase-Sum Reduction to `rSum7`**. -/
theorem omega128_sum_217_pointAxisPhaseExp128_eq_of_rSum7 (z : Fin 64) (u : Fin 217 → Fin 64)
    (s : Fin 128) (hSum : (∑ e : Fin 217, (u e).val) % 128 = s.val) : omega128
    (∑ e : Fin 217, pointAxisPhaseExp128 z (u e)) = omega128 (pointCrossXorExp128 z s) *
    omega128 (pointTargetOnlyExp128 z) * omega128 (pointSumCliffordExp128 z s) * omega128
    (∑ e : Fin 217, pointElecCliffordExp128 (u e)) := by
  have h1 : omega128 (∑ e : Fin 217, pointAxisPhaseExp128 z (u e)) = omega128 ((31 - 2 *
      ((bitRev6 z).val : ℤ)) * (∑ e : Fin 217, ((u e).val : ℤ))) * omega128 (∑ e : Fin 217,
      (32 * ∑ r : Fin 6, (1 - ((2 ^ r.val : ℕ) : ℤ)) * (bit6 (u e) r : ℤ))) := by
    rw [← omega128_add]
    apply congrArg omega128
    unfold pointAxisPhaseExp128
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hMod : (∑ e : Fin 217, ((u e).val : ℤ)) % 128 = (s.val : ℤ) := by
    have hcast : (∑ e : Fin 217, ((u e).val : ℤ)) = ((∑ e : Fin 217, (u e).val : ℕ) : ℤ) :=
      (Nat.cast_sum _ _).symm
    rw [hcast]
    omega
  have hLin : omega128 ((31 - 2 * ((bitRev6 z).val : ℤ)) * (∑ e : Fin 217, ((u e).val : ℤ))) =
      omega128 (pointCrossXorExp128 z s) * omega128 (pointTargetOnlyExp128 z) * omega128
      (pointSumCliffordExp128 z s) := by
    rw [omega128_mul_int_emod_128, hMod, omega128_pointLinearMul_eq]
  have hCliff : omega128 (∑ e : Fin 217, (32 * ∑ r : Fin 6, (1 - ((2 ^ r.val : ℕ) : ℤ)) *
      (bit6 (u e) r : ℤ))) = omega128 (∑ e : Fin 217, pointElecCliffordExp128 (u e)) :=
    omega128_sum_congr_emod Finset.univ _ _ fun e _ ↦ pointElecCliffordExp128_emod_128_eq (u e)
  rw [h1, hLin, hCliff]
/-- Core register slice `[0 .. fullSysCoreWires mPayload)` inside `fullSysCoreWires mPayload +
  42`. -/
def rCoreInCoreSum42 (mPayload : ℕ) :
    QRegister (fullSysCoreWires mPayload) (fullSysCoreWires mPayload + 42) :=
  QRegister.block 0 (fullSysCoreWires mPayload) (by omega)
/-- Per-axis 14-bit sum register slice `[fullSysCoreWires mPayload + 14 * w .. + 14)` inside
`fullSysCoreWires mPayload + 42`. -/
def rSum14InCoreSum42 (mPayload : ℕ) (w : Fin 3) :
    QRegister 14 (fullSysCoreWires mPayload + 42) :=
  QRegister.block (fullSysCoreWires mPayload + 14 * w.val) 14 (by have := w.isLt; omega)
/-- Generic 3-axis 42-wire sum subspace projector on `fullSysCoreWires mPayload + 42`. -/
noncomputable def pStream42Of {mPayload : ℕ}
    (sumFn : Fin 3 → BitAssignment (fullSysCoreWires mPayload) → ℕ) :
    Operator (2 ^ (fullSysCoreWires mPayload + 42)) :=
  Matrix.diagonal fun x ↦
    let ξ := basisBits (fullSysCoreWires mPayload + 42) x
    let γ : BitAssignment (fullSysCoreWires mPayload) := fun q ↦ ξ (rCoreInCoreSum42 mPayload q)
    if ∀ w : Fin 3, regVal (rSum14InCoreSum42 mPayload w) ξ = sumFn w γ then (1 : ℂ) else 0
/-- 218-electron momentum-sum subspace projector `pStream218Core` (`rSum14(w) = slot2AxisSum w
  γ`). -/
noncomputable def pStream218Core (mPayload : ℕ) :
    Operator (2 ^ (fullSysCoreWires mPayload + 42)) :=
  pStream42Of (mPayload := mPayload) slot2AxisSum
/-- 217-electron spectator momentum-sum subspace projector `pStream217Core`
(`rSum14(w) = spectatorSum217 w γ = ∑_{e=1}^{217} u_{e,w}`). -/
noncomputable def pStream217Core (mPayload : ℕ) :
    Operator (2 ^ (fullSysCoreWires mPayload + 42)) :=
  pStream42Of (mPayload := mPayload) spectatorSum217
/-- Width-parametric `FullSysQft654Bundle` for the `117-T` 1-electron Hadamard-Forest `QFT_64`
(`tQft = 117`, `2 * tQft = 234 T/step`, `TOFF = 0`, saving **`-26 T/step = -41.5 Tq`** below
`activeOneElecQftBundle`'s `130 T`). -/
noncomputable def activeOneElecForestQftBundle (mWork : ℕ) (hm : 128 ≤ mWork) :
    FullSysCatSegmentBridge.FullSysQft654Bundle :=
  toFullSysQft654BundleOfLe128 activeOneElecForestFullQftStage128 mWork hm
/-- Turnkey `mWorkQft = 128` 1-electron Hadamard-Forest `FullSysQft654Bundle` (`tQft = 117`, `234
  T/step`, `TOFF = 0`). -/
noncomputable abbrev activeOneElecForestQftBundle128 :
    FullSysCatSegmentBridge.FullSysQft654Bundle :=
  activeOneElecForestQftBundle 128 le_rfl
@[simp] theorem activeOneElecForestQftBundle_mWorkQft (mWork : ℕ) (hm : 128 ≤ mWork) :
    (activeOneElecForestQftBundle mWork hm).mWorkQft = mWork := rfl
@[simp] theorem activeOneElecForestQftBundle_uQft654 (mWork : ℕ) (hm : 128 ≤ mWork) :
    (activeOneElecForestQftBundle mWork hm).uQft654 =
      axisProdPrefix 3 hL3_le_654 (fun _ ↦ uCoreHadamard6) := rfl
@[simp] theorem activeOneElecForestQftBundle128_mWorkQft :
    activeOneElecForestQftBundle128.mWorkQft = 128 := rfl
end ConfigK7
end ForestQft117BundleNoTopBridge
namespace ElecHadConjLoadAndTrueSwapComp
open SpecsAux SpecsAux.SpecMirror
open scoped Circuit.Notation
section Impl07a
set_option maxRecDepth 65536
/-- Abstract 18-bit slot lens `(tbl, updSlot)` on `Fin (2 ^ kData)` capturing any indexed slot bank
(such as the 218-electron anchor bank or 217-electron partner bank). -/
structure Slot18Lens (kData : ℕ) where
  tbl : Fin (2 ^ kData) → Fin (2 ^ 18)
  updSlot : Fin (2 ^ kData) → Fin (2 ^ 18) → Fin (2 ^ kData)
  get_put : ∀ d v, tbl (updSlot d v) = v
  put_get : ∀ d, updSlot d (tbl d) = d
  put_put : ∀ d v₁ v₂, updSlot (updSlot d v₁) v₂ = updSlot d v₂
/-- True swap map `(d, y) ↦ (updSlot d y, tbl d)` exchanging the active slot in `d` with `y`. -/
noncomputable def lensSwapPerm {kData : ℕ} (L : Slot18Lens kData)
    (p : Fin (2 ^ kData) × Fin (2 ^ 18)) : Fin (2 ^ kData) × Fin (2 ^ 18) :=
  (L.updSlot p.1 p.2, L.tbl p.1)
theorem lensSwapPerm_involutive {kData : ℕ} (L : Slot18Lens kData) :
    Function.Involutive (lensSwapPerm L) := by
  rintro ⟨d, y⟩
  dsimp only [lensSwapPerm]
  rw [L.get_put, L.put_put, L.put_get]
end Impl07a
end ElecHadConjLoadAndTrueSwapComp
set_option maxRecDepth 65536
namespace ElecHadTrueSwapHCompClosure
section Impl02l
open HermitianMat
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open PosSlots24BranchConcrete (posCoreWires)
open InterWalkRSum42Hoist (h3924_core)
/-- Proof that `3924 ≤ posCoreWires`. -/
theorem h3924_le_posCoreWires : 3924 ≤ posCoreWires := by
  rw [← PosSlots24SemanticBridge.pos24_coreWires80_eq]
  exact h3924_core
end Impl02l
end ElecHadTrueSwapHCompClosure
namespace ZeroHypElecHadHCompAndPass123Closure
section Impl02m
open HermitianMat
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open InterWalkRSum42Hoist (qreg_block_apply)
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens lensSwapPerm
  lensSwapPerm_involutive)
/-- Permutation matrix `P_{i, j} = [i = f j]` on `Fin d`. -/
def permMatrix {d : ℕ} (f : Fin d → Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j ↦ if i = f j then 1 else 0
theorem permMatrix_mul {d : ℕ} (f g : Fin d → Fin d) :
    permMatrix f * permMatrix g = permMatrix (f ∘ g) := by
  ext i j
  simp only [permMatrix, Matrix.mul_apply, Matrix.of_apply, Function.comp_apply]
  rw [Finset.sum_eq_single (g j)]
  · simp
  · intro m _ hm
    rw [ite_eq_right hm, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ (g j)) h
theorem permMatrix_id {d : ℕ} : permMatrix (id : Fin d → Fin d) = (1 : Matrix (Fin d) (Fin d) ℂ) :=
    by
  ext i j
  simp [permMatrix, Matrix.one_apply]
theorem permMatrix_conjTranspose_of_involutive {d : ℕ} {f : Fin d → Fin d}
    (hf : Function.Involutive f) : (permMatrix f)ᴴ = permMatrix f := by
  ext i j
  simp only [permMatrix, Matrix.conjTranspose_apply, Matrix.of_apply]
  have hiff : j = f i ↔ i = f j := ⟨fun h ↦ by rw [h, hf i], fun h ↦ by rw [h, hf j]⟩
  by_cases h : i = f j
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h, star_one]
  · rw [ite_eq_right (fun hj ↦ h (hiff.mp hj)), ite_eq_right h, star_zero]
theorem permMatrix_mem_unitaryGroup {d : ℕ} {f : Fin d → Fin d}
    (hf : Function.Involutive f) : permMatrix f ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have hcomp : f ∘ f = id := funext hf
  rw [star_eq_conjTranspose, permMatrix_conjTranspose_of_involutive hf,
      permMatrix_mul, hcomp, permMatrix_id]
/-- Unitary operator induced by any involutive permutation `f : Fin d → Fin d`. -/
noncomputable def permUnitary {d : ℕ} (f : Fin d → Fin d) (hf : Function.Involutive f) : Unitary d
    :=
  ⟨permMatrix f, permMatrix_mem_unitaryGroup hf⟩
/-- Splits `z : Fin (2 ^ (kData + 18))` into `(d, y) : Fin (2 ^ kData) × Fin (2 ^ 18)`. -/
noncomputable def splitDM {kData : ℕ} (z : Fin (2 ^ (kData + 18))) : Fin (2 ^ kData) × Fin
    (2 ^ 18) := ((selDataInAct kData).extractIndex z, (selMeasInAct kData).extractIndex z)
/-- Joins `(d, y) : Fin (2 ^ kData) × Fin (2 ^ 18)` into `Fin (2 ^ (kData + 18))`. -/
noncomputable def joinDM {kData : ℕ} (p : Fin (2 ^ kData) × Fin (2 ^ 18)) :
    Fin (2 ^ (kData + 18)) :=
  (basisBitsEquiv (kData + 18)).symm (Fin.addCases (basisBits kData p.1) (basisBits 18 p.2))
@[simp] theorem splitDM_joinDM {kData : ℕ} (p : Fin (2 ^ kData) × Fin (2 ^ 18)) :
    splitDM (joinDM p) = p := by
  have hSymm : ∀ idx : Fin (kData + 18), basisBits (kData + 18) (joinDM p) idx = Fin.addCases
      (basisBits kData p.1) (basisBits 18 p.2) idx := fun idx ↦ congrFun
      ((basisBitsEquiv (kData + 18)).apply_symm_apply _) idx
  rcases p with ⟨d, y⟩
  ext
  · refine Fin.val_eq_of_eq ((basisBitsEquiv kData).injective ?_)
    funext i
    change basisBits kData ((selDataInAct kData).extractIndex (joinDM (d, y))) i = basisBits kData
        d i
    rw [QRegister.basisBits_extractIndex]
    have hi : selDataInAct kData i = Fin.castAdd 18 i :=
      Fin.ext (by simp [selDataInAct])
    rw [hi, hSymm (Fin.castAdd 18 i), Fin.addCases_left]
  · refine Fin.val_eq_of_eq ((basisBitsEquiv 18).injective ?_)
    funext j
    change basisBits 18 ((selMeasInAct kData).extractIndex (joinDM (d, y))) j = basisBits 18 y j
    rw [QRegister.basisBits_extractIndex]
    have hj : selMeasInAct kData j = Fin.natAdd kData j :=
      Fin.ext (by simp [selMeasInAct])
    rw [hj, hSymm (Fin.natAdd kData j), Fin.addCases_right]
@[simp] theorem joinDM_splitDM {kData : ℕ} (z : Fin (2 ^ (kData + 18))) :
    joinDM (splitDM z) = z := by
  have hSymm : ∀ idx : Fin (kData + 18), basisBits (kData + 18) (joinDM (splitDM z)) idx =
      Fin.addCases (basisBits kData (splitDM z).1) (basisBits 18 (splitDM z).2) idx := fun idx
      ↦ congrFun ((basisBitsEquiv (kData + 18)).apply_symm_apply _) idx
  apply (basisBitsEquiv (kData + 18)).injective
  funext idx
  change basisBits (kData + 18) (joinDM (splitDM z)) idx = basisBits (kData + 18) z idx
  rw [hSymm idx]
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
  · rw [Fin.addCases_left]
    dsimp only [splitDM]
    rw [QRegister.basisBits_extractIndex]
    have hi : selDataInAct kData i = Fin.castAdd 18 i :=
      Fin.ext (by simp [selDataInAct])
    rw [hi]
  · rw [Fin.addCases_right]
    dsimp only [splitDM]
    rw [QRegister.basisBits_extractIndex]
    have hj : selMeasInAct kData j = Fin.natAdd kData j :=
      Fin.ext (by simp [selMeasInAct])
    rw [hj]
/-- Fin-level true swap involution induced by `L : Slot18Lens kData`. -/
noncomputable def lensSwapFin {kData : ℕ} (L : Slot18Lens kData) (z : Fin (2 ^ (kData + 18)))
    : Fin (2 ^ (kData + 18)) := joinDM (lensSwapPerm L (splitDM z))
theorem lensSwapFin_involutive {kData : ℕ} (L : Slot18Lens kData) :
    Function.Involutive (lensSwapFin L) := fun z ↦ by
  dsimp only [lensSwapFin]
  rw [splitDM_joinDM, lensSwapPerm_involutive L, joinDM_splitDM]
/-- Unitary `uLensSwap L : Unitary (2 ^ (kData + 18))` for any `L : Slot18Lens kData`. -/
noncomputable def uLensSwap {kData : ℕ} (L : Slot18Lens kData) : Unitary (2 ^ (kData + 18)) :=
  permUnitary (lensSwapFin L) (lensSwapFin_involutive L)
end Impl02m
end ZeroHypElecHadHCompAndPass123Closure
end SharedScope
end
end SlimStageADepsC

noncomputable section SlimStageADepsD

section
set_option maxRecDepth 131072
set_option exponentiation.threshold 256
section SharedScope
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup
local instance (priority := 1000000) instNeZeroExt (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix _root_.DynamicCircuit DynCircuitExt Real
open Circuit hiding TOFF
open scoped Matrix BigOperators
open StageADeconstrCore (selDataInAct selMeasInAct selDataInAct_disj_selMeasInAct)
attribute [local reducible]
  SpecsAux.SpecMirror.numElectrons
  SpecsAux.SpecMirror.systemQubits
  InterWalkRSum42Hoist.mActHoist
  HarmonicScheduleBridge.hoAncillasM
section XorForestStageABody
namespace Origin0Head34RealizesAndLeaf2Spec
open HermitianMat LocalClassicalPerm
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open SpecsAux SpecsAux.SpecMirror
section Part1_Origin0Head34Realizes
set_option maxRecDepth 131072
set_option exponentiation.threshold 8192
open OctahedralOrbit
open CanonRank7Circuit
open BchCubeDecoder PosSlots24BranchConcrete
open GridGuard654ReflAux (symStepFwdList symStepFwdList_cons ValidSymStepList polBit litAndSymStep
  litAndSymStep_stepFwd)
open PosSlots24CompactHead123 PosHeadRev18CacheAux PosHeadMod4_15476
open OriginZeroHeadMod4Reduction (zeroSlot0Bits)
theorem nuc_ne_scr {n mScr : ℕ} (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (i : Fin 8) (j : Fin mScr) : rNucIdx rCore i ≠ rScr j :=
    hCS.ne _ j
theorem anc_ne_scr {n mScr : ℕ} (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (i : Fin 8) (j : Fin mScr) : rAnchorIdx rCore i ≠ rScr j
    := hCS.ne _ j
theorem wSlot0_ne_scr {n mScr : ℕ} (rCore : QRegister posCoreWires n)
    (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rScr) (j : Fin mScr) : wSlot0Core
    rCore ≠ rScr j := hCS.ne _ j
theorem wSlot1_ne_scr {n mScr : ℕ} (rCore : QRegister posCoreWires n)
    (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rScr) (j : Fin mScr) : wSlot1Core
    rCore ≠ rScr j := hCS.ne _ j
theorem wSlot2_ne_scr {n mScr : ℕ} (rCore : QRegister posCoreWires n)
    (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rScr) (j : Fin mScr) : wSlot2Core
    rCore ≠ rScr j := hCS.ne _ j
theorem wSubReject_ne_scr {n mScr : ℕ} (rCore : QRegister posCoreWires n)
    (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rScr) (j : Fin mScr) : wSubReject
    rCore ≠ rScr j := hCS.ne _ j
theorem wIsHead_ne_scr {n mScr : ℕ} (rCore : QRegister posCoreWires n)
    (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rScr) (j : Fin mScr) : wIsHead rCore
    ≠ rScr j := hCS.ne _ j
theorem wHeadThresh_ne_scr {n mScr : ℕ} (rCore : QRegister posCoreWires n)
    (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rScr) (j : Fin mScr) : wHeadThresh
    rCore ≠ rScr j := hCS.ne _ j
/-- The `16` head-enable `TempAnd` steps (`rScr[0 .. 15]`, `4 * 16 = 64 T`, `0 TOFF`,
100% disjoint from `wHeadThresh rCore`). -/
def origin0HeadEnSteps16 {n mScr : ℕ} (hm16 : 16 ≤ mScr) (rCore : QRegister posCoreWires n)
    (rScr : QRegister mScr n) (hCS : rCore.DisjointWires rScr) : List (SymTempAndStep n) :=
  let x := rNucIdx rCore
  let y := rAnchorIdx rCore
  have hw_ne : ∀ (a b : ℕ) (ha : a < mScr) (hb : b < mScr), a ≠ b → rScr ⟨a, ha⟩ ≠ rScr ⟨b, hb⟩ :=
    fun a b _ _ h heq ↦ h (congrArg Fin.val (rScr.wires.injective heq));
  [ litAndSymStep false false false (x 4) (x 3) (rScr ⟨0, by omega⟩)
      (phcHead_nuc_ne_core rCore 4 3 (by decide)) (nuc_ne_scr rCore rScr hCS 4 _) (nuc_ne_scr rCore
          rScr hCS 3 _),
    litAndSymStep true true true (x 5) (rScr ⟨0, by omega⟩) (rScr ⟨1, by omega⟩)
      (nuc_ne_scr rCore rScr hCS 5 _) (nuc_ne_scr rCore rScr hCS 5 _) (hw_ne 0 1 _ _ (by decide)),
    litAndSymStep false false false (x 7) (x 6) (rScr ⟨2, by omega⟩)
      (phcHead_nuc_ne_core rCore 7 6 (by decide)) (nuc_ne_scr rCore rScr hCS 7 _) (nuc_ne_scr rCore
          rScr hCS 6 _),
    litAndSymStep false false true (rScr ⟨2, by omega⟩) (rScr ⟨1, by omega⟩) (rScr ⟨3, by omega⟩)
      (hw_ne 2 1 _ _ (by decide)) (hw_ne 2 3 _ _ (by decide)) (hw_ne 1 3 _ _ (by decide)),
    litAndSymStep true true true (y 2) (y 1) (rScr ⟨4, by omega⟩)
      (phcHead_anc_ne_core rCore 2 1 (by decide)) (anc_ne_scr rCore rScr hCS 2 _) (anc_ne_scr rCore
          rScr hCS 1 _),
    litAndSymStep false false false (y 4) (y 3) (rScr ⟨5, by omega⟩)
      (phcHead_anc_ne_core rCore 4 3 (by decide)) (anc_ne_scr rCore rScr hCS 4 _) (anc_ne_scr rCore
          rScr hCS 3 _),
    litAndSymStep false false false (rScr ⟨5, by omega⟩) (rScr ⟨4, by omega⟩) (rScr ⟨6, by omega⟩)
      (hw_ne 5 4 _ _ (by decide)) (hw_ne 5 6 _ _ (by decide)) (hw_ne 4 6 _ _ (by decide)),
    litAndSymStep true true true (y 5) (rScr ⟨6, by omega⟩) (rScr ⟨7, by omega⟩)
      (anc_ne_scr rCore rScr hCS 5 _) (anc_ne_scr rCore rScr hCS 5 _) (hw_ne 6 7 _ _ (by decide)),
    litAndSymStep false false false (y 7) (y 6) (rScr ⟨8, by omega⟩)
      (phcHead_anc_ne_core rCore 7 6 (by decide)) (anc_ne_scr rCore rScr hCS 7 _) (anc_ne_scr rCore
          rScr hCS 6 _),
    litAndSymStep false false true (rScr ⟨8, by omega⟩) (rScr ⟨7, by omega⟩) (rScr ⟨9, by omega⟩)
      (hw_ne 8 7 _ _ (by decide)) (hw_ne 8 9 _ _ (by decide)) (hw_ne 7 9 _ _ (by decide)),
    litAndSymStep true true true (wSlot0Core rCore) (rScr ⟨3, by omega⟩) (rScr ⟨10, by omega⟩)
      (wSlot0_ne_scr rCore rScr hCS _) (wSlot0_ne_scr rCore rScr hCS _) (hw_ne 3 10 _ _ (by
          decide)),
    litAndSymStep true true false (wSlot2Core rCore) (wSlot1Core rCore) (rScr ⟨11, by omega⟩)
      (phcHead_wSlot2_ne_wSlot1 rCore) (wSlot2_ne_scr rCore rScr hCS _) (wSlot1_ne_scr rCore rScr
          hCS _),
    litAndSymStep true false false (wSubReject rCore) (rScr ⟨9, by omega⟩) (rScr ⟨12, by omega⟩)
      (wSubReject_ne_scr rCore rScr hCS _)
      (wSubReject_ne_scr rCore rScr hCS _)
      (hw_ne 9 12 _ _ (by decide)),
    litAndSymStep false false false (rScr ⟨10, by omega⟩) (wIsHead rCore) (rScr ⟨13, by omega⟩)
      (wIsHead_ne_scr rCore rScr hCS _).symm
      (hw_ne 10 13 _ _ (by decide))
      (wIsHead_ne_scr rCore rScr hCS _),
    litAndSymStep false false false (rScr ⟨11, by omega⟩) (rScr ⟨12, by omega⟩) (rScr ⟨14, by
        omega⟩)
      (hw_ne 11 12 _ _ (by decide)) (hw_ne 11 14 _ _ (by decide)) (hw_ne 12 14 _ _ (by decide)),
    litAndSymStep false false false (rScr ⟨14, by omega⟩) (rScr ⟨13, by omega⟩) (rScr ⟨15, by
        omega⟩)
      (hw_ne 14 13 _ _ (by decide)) (hw_ne 14 15 _ _ (by decide)) (hw_ne 13 15 _ _ (by decide)) ]
@[simp] theorem length_origin0HeadEnSteps16 {n mScr : ℕ} (hm16 : 16 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) : (origin0HeadEnSteps16 hm16 rCore rScr hCS).length = 16
    := rfl
theorem nuc_mem_core_union {n : ℕ} {S : Finset (Wire n)} (rCore : QRegister posCoreWires n) (i :
    Fin 8) :
    rNucIdx rCore i ∈ rCore.image ∪ S :=
  Finset.mem_union_left _
    (slice_image_subset rCore _ (slice_image_subset _ _ (QRegister.mem_image _ _ |>.mpr ⟨i, rfl⟩)))
theorem anc_mem_core_union {n : ℕ} {S : Finset (Wire n)} (rCore : QRegister posCoreWires n) (i :
    Fin 8) :
    rAnchorIdx rCore i ∈ rCore.image ∪ S :=
  Finset.mem_union_left _
    (slice_image_subset rCore _ (slice_image_subset _ _ (QRegister.mem_image _ _ |>.mpr ⟨i, rfl⟩)))
theorem wSlot0_mem_core_union {n : ℕ} {S : Finset (Wire n)} (rCore : QRegister posCoreWires n) :
    wSlot0Core rCore ∈ rCore.image ∪ S :=
  Finset.mem_union_left _ (QRegister.mem_image rCore _ |>.mpr ⟨_, rfl⟩)
theorem wSlot1_mem_core_union {n : ℕ} {S : Finset (Wire n)} (rCore : QRegister posCoreWires n) :
    wSlot1Core rCore ∈ rCore.image ∪ S :=
  Finset.mem_union_left _ (QRegister.mem_image rCore _ |>.mpr ⟨_, rfl⟩)
theorem wSlot2_mem_core_union {n : ℕ} {S : Finset (Wire n)} (rCore : QRegister posCoreWires n) :
    wSlot2Core rCore ∈ rCore.image ∪ S :=
  Finset.mem_union_left _ (QRegister.mem_image rCore _ |>.mpr ⟨_, rfl⟩)
theorem wSubReject_mem_core_union {n : ℕ} {S : Finset (Wire n)} (rCore : QRegister posCoreWires n) :
    wSubReject rCore ∈ rCore.image ∪ S :=
  Finset.mem_union_left _
    (slice_image_subset rCore _ (QRegister.mem_image _ _ |>.mpr ⟨_, rfl⟩))
theorem wIsHead_mem_core_union {n : ℕ} {S : Finset (Wire n)} (rCore : QRegister posCoreWires n) :
    wIsHead rCore ∈ rCore.image ∪ S :=
  Finset.mem_union_left _
    (slice_image_subset rCore _ (QRegister.mem_image _ _ |>.mpr ⟨_, rfl⟩))
theorem origin0HeadEnSteps16_valid_and_sub {n mScr : ℕ} (hm16 : 16 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) : ValidSymStepList (∅ : Finset (Wire n)) rScr 0
    (origin0HeadEnSteps16 hm16 rCore rScr hCS) ∧ (∀ s ∈ origin0HeadEnSteps16 hm16 rCore rScr
    hCS, s.S ⊆ rCore.image ∪ (rScr.slice 0 16 hm16).image) := by
  have latW : ∀ (a : ℕ) (ha : a < mScr) (idx : Fin mScr), a < idx.val → rScr idx ≠ rScr ⟨a, ha⟩ :=
    fun a _ idx hlt h ↦ (Nat.ne_of_gt hlt) (congrArg Fin.val (rScr.wires.injective h))
  have mem16 : ∀ (k : ℕ) (hk : k < 16) (hk' : k < mScr),
      rScr ⟨k, hk'⟩ ∈ rCore.image ∪ (rScr.slice 0 16 hm16).image :=
    fun k hk _ ↦ Finset.mem_union_right _ (QRegister.mem_image _ _ |>.mpr ⟨⟨k, hk⟩,
      congrArg rScr.wires (Fin.ext (by dsimp [QRegister.slice_apply]; omega))⟩)
  constructor
  · dsimp only [origin0HeadEnSteps16, ValidSymStepList, phcHead_litAndSymStep_anc,
      phcHead_litAndSymStep_S]
    refine ⟨by omega, rfl, Finset.disjoint_empty_right _, ?_,
      ⟨by omega, rfl, Finset.disjoint_empty_right _, ?_,
      ⟨by omega, rfl, Finset.disjoint_empty_right _, ?_,
      ⟨by omega, rfl, Finset.disjoint_empty_right _, ?_,
      ⟨by omega, rfl, Finset.disjoint_empty_right _, ?_,
      ⟨by omega, rfl, Finset.disjoint_empty_right _, ?_,
      ⟨by omega, rfl, Finset.disjoint_empty_right _, ?_,
      ⟨by omega, rfl, Finset.disjoint_empty_right _, ?_,
      ⟨by omega, rfl, Finset.disjoint_empty_right _, ?_,
      ⟨by omega, rfl, Finset.disjoint_empty_right _, ?_,
      ⟨by omega, rfl, Finset.disjoint_empty_right _, ?_,
      ⟨by omega, rfl, Finset.disjoint_empty_right _, ?_,
      ⟨by omega, rfl, Finset.disjoint_empty_right _, ?_,
      ⟨by omega, rfl, Finset.disjoint_empty_right _, ?_,
      ⟨by omega, rfl, Finset.disjoint_empty_right _, ?_,
      ⟨by omega, rfl, Finset.disjoint_empty_right _, ?_, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
    all_goals
      intro idx hlt
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨?_, ?_, latW _ _ idx (by omega)⟩
      all_goals
        first
        | (with_reducible refine latW _ _ idx ?_); omega
        | with_reducible exact (nuc_ne_scr rCore rScr hCS _ idx).symm
        | with_reducible exact (anc_ne_scr rCore rScr hCS _ idx).symm
        | with_reducible exact (wSlot0_ne_scr rCore rScr hCS idx).symm
        | with_reducible exact (wSlot1_ne_scr rCore rScr hCS idx).symm
        | with_reducible exact (wSlot2_ne_scr rCore rScr hCS idx).symm
        | with_reducible exact (wSubReject_ne_scr rCore rScr hCS idx).symm
        | with_reducible exact (wIsHead_ne_scr rCore rScr hCS idx).symm
  · intro s hs
    dsimp only [origin0HeadEnSteps16] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      intro z hz
      simp only [phcHead_litAndSymStep_S, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      all_goals
        first
        | (with_reducible refine mem16 _ ?_ _); omega
        | with_reducible exact nuc_mem_core_union rCore _
        | with_reducible exact anc_mem_core_union rCore _
        | with_reducible exact wSlot0_mem_core_union rCore
        | with_reducible exact wSlot1_mem_core_union rCore
        | with_reducible exact wSlot2_mem_core_union rCore
        | with_reducible exact wSubReject_mem_core_union rCore
        | with_reducible exact wIsHead_mem_core_union rCore
theorem wHeadThresh_not_mem_origin0HeadEnSteps16 {n mScr : ℕ} (hm16 : 16 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) :
    ∀ s ∈ origin0HeadEnSteps16 hm16 rCore rScr hCS, wHeadThresh rCore ∉ s.S := by
  intro s hs
  dsimp only [origin0HeadEnSteps16] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [phcHead_litAndSymStep_S, Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨?_, ?_, wHeadThresh_ne_scr rCore rScr hCS _⟩
    all_goals
      first
      | exact wHeadThresh_ne_rNucIdx rCore _
      | exact wHeadThresh_ne_rAnchorIdx rCore _
      | exact wHeadThresh_ne_wSlot0Core rCore
      | exact wHeadThresh_ne_wSlot1Core rCore
      | exact wHeadThresh_ne_wSlot2Core rCore
      | exact wHeadThresh_ne_wSubReject rCore
      | exact wHeadThresh_ne_wIsHead rCore
      | exact wHeadThresh_ne_scr rCore rScr hCS _
theorem polBit_headEnBoolSpec_eq {n : ℕ} (rCore : QRegister posCoreWires n)
    (β : BitAssignment n) : polBit false (polBit false (polBit false (polBit false (polBit
    true (β (wSlot2Core rCore)) * polBit true (β (wSlot1Core rCore))) * polBit false (polBit
    true (β (wSubReject rCore)) * polBit false (if decide (regVal (rAnchorIdx rCore) β < 218)
    then 1 else 0)))) * polBit false (polBit false (polBit true (polBit true (β (wSlot0Core
    rCore)) * polBit true (if decide (regVal (rNucIdx rCore) β < 216) then 1 else 0))) *
    polBit false (β (wIsHead rCore)))) = if headEnBoolSpec (fun i ↦ β (rCore i)) then 1 else 0
    := by
  rw [← headEnRaw_eq_headEnBoolSpec rCore β,
      phcHead_decide_imp_lt_eq (Bool.not (β (wSlot0Core rCore) == 1)) (regVal (rNucIdx rCore) β <
          216)]
  exact phcHead_zmod2_polBit_headEn_eval (decide (regVal (rNucIdx rCore) β < 216))
    (decide (regVal (rAnchorIdx rCore) β < 218)) (β (wSlot0Core rCore)) (β (wSlot1Core rCore))
    (β (wSlot2Core rCore)) (β (wSubReject rCore)) (β (wIsHead rCore))
theorem origin0HeadEnSteps16_eval {n mScr : ℕ} (hm16 : 16 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr)
    (β : BitAssignment n) (hClean16 : ∀ idx : Fin 16, β (rScr ⟨idx.val, by omega⟩) = 0) :
    (∀ z, z ∉ (rScr.slice 0 16 hm16).image →
      (symStepFwdList (origin0HeadEnSteps16 hm16 rCore rScr hCS) β) z = β z) ∧
    (symStepFwdList (origin0HeadEnSteps16 hm16 rCore rScr hCS) β) (rScr ⟨15, by omega⟩) =
      (if headEnBoolSpec (fun i ↦ β (rCore i)) then 1 else 0) := by
  let x := rNucIdx rCore
  let y := rAnchorIdx rCore
  have hw_ne : ∀ (a b : ℕ) (ha : a < mScr) (hb : b < mScr), a ≠ b → rScr ⟨a, ha⟩ ≠ rScr ⟨b, hb⟩ :=
    fun a b _ _ h heq ↦ h (congrArg Fin.val (rScr.wires.injective heq))
  have hc16 : ∀ (k : ℕ) (hk : k < 16) (hk' : k < mScr), β (rScr ⟨k, hk'⟩) = 0 :=
    fun k hk _ ↦ hClean16 ⟨k, hk⟩
  let u0 := Function.update β (rScr ⟨0, by omega⟩) (polBit false (polBit false (β (x 4)) * polBit
      false (β (x 3))))
  have hi0 : ∀ (k : ℕ) (_ : 0 < k) (hk16 : k < 16) (hk' : k < mScr), u0 (rScr ⟨k, hk'⟩) = 0 :=
    fun k hk hk16 _ ↦ by dsimp only [u0]; rw [Function.update_of_ne (hw_ne k 0 _ _ (by omega)),
        hc16 k hk16 _]
  let u1 := Function.update u0 (rScr ⟨1, by omega⟩) (polBit true (polBit true (u0 (x 5)) * polBit
      true (u0 (rScr ⟨0, by omega⟩))))
  have hi1 : ∀ (k : ℕ) (_ : 1 < k) (hk16 : k < 16) (hk' : k < mScr), u1 (rScr ⟨k, hk'⟩) = 0 :=
    fun k hk hk16 _ ↦ by dsimp only [u1]; rw [Function.update_of_ne (hw_ne k 1 _ _ (by omega)), hi0
        k (by omega) hk16 _]
  let u2 := Function.update u1 (rScr ⟨2, by omega⟩) (polBit false (polBit false (u1 (x 7)) * polBit
      false (u1 (x 6))))
  have hi2 : ∀ (k : ℕ) (_ : 2 < k) (hk16 : k < 16) (hk' : k < mScr), u2 (rScr ⟨k, hk'⟩) = 0 :=
    fun k hk hk16 _ ↦ by dsimp only [u2]; rw [Function.update_of_ne (hw_ne k 2 _ _ (by omega)), hi1
        k (by omega) hk16 _]
  let u3 := Function.update u2 (rScr ⟨3, by omega⟩) (polBit true (polBit false (u2 (rScr ⟨2, by
      omega⟩)) * polBit false (u2 (rScr ⟨1, by omega⟩))))
  have hi3 : ∀ (k : ℕ) (_ : 3 < k) (hk16 : k < 16) (hk' : k < mScr), u3 (rScr ⟨k, hk'⟩) = 0 :=
    fun k hk hk16 _ ↦ by dsimp only [u3]; rw [Function.update_of_ne (hw_ne k 3 _ _ (by omega)), hi2
        k (by omega) hk16 _]
  let u4 := Function.update u3 (rScr ⟨4, by omega⟩) (polBit true (polBit true (u3 (y 2)) * polBit
      true (u3 (y 1))))
  have hi4 : ∀ (k : ℕ) (_ : 4 < k) (hk16 : k < 16) (hk' : k < mScr), u4 (rScr ⟨k, hk'⟩) = 0 :=
    fun k hk hk16 _ ↦ by dsimp only [u4]; rw [Function.update_of_ne (hw_ne k 4 _ _ (by omega)), hi3
        k (by omega) hk16 _]
  let u5 := Function.update u4 (rScr ⟨5, by omega⟩) (polBit false (polBit false (u4 (y 4)) * polBit
      false (u4 (y 3))))
  have hi5 : ∀ (k : ℕ) (_ : 5 < k) (hk16 : k < 16) (hk' : k < mScr), u5 (rScr ⟨k, hk'⟩) = 0 :=
    fun k hk hk16 _ ↦ by dsimp only [u5]; rw [Function.update_of_ne (hw_ne k 5 _ _ (by omega)), hi4
        k (by omega) hk16 _]
  let u6 := Function.update u5 (rScr ⟨6, by omega⟩) (polBit false (polBit false (u5 (rScr ⟨5, by
      omega⟩)) * polBit false (u5 (rScr ⟨4, by omega⟩))))
  have hi6 : ∀ (k : ℕ) (_ : 6 < k) (hk16 : k < 16) (hk' : k < mScr), u6 (rScr ⟨k, hk'⟩) = 0 :=
    fun k hk hk16 _ ↦ by dsimp only [u6]; rw [Function.update_of_ne (hw_ne k 6 _ _ (by omega)), hi5
        k (by omega) hk16 _]
  let u7 := Function.update u6 (rScr ⟨7, by omega⟩) (polBit true (polBit true (u6 (y 5)) * polBit
      true (u6 (rScr ⟨6, by omega⟩))))
  have hi7 : ∀ (k : ℕ) (_ : 7 < k) (hk16 : k < 16) (hk' : k < mScr), u7 (rScr ⟨k, hk'⟩) = 0 :=
    fun k hk hk16 _ ↦ by dsimp only [u7]; rw [Function.update_of_ne (hw_ne k 7 _ _ (by omega)), hi6
        k (by omega) hk16 _]
  let u8 := Function.update u7 (rScr ⟨8, by omega⟩) (polBit false (polBit false (u7 (y 7)) * polBit
      false (u7 (y 6))))
  have hi8 : ∀ (k : ℕ) (_ : 8 < k) (hk16 : k < 16) (hk' : k < mScr), u8 (rScr ⟨k, hk'⟩) = 0 :=
    fun k hk hk16 _ ↦ by dsimp only [u8]; rw [Function.update_of_ne (hw_ne k 8 _ _ (by omega)), hi7
        k (by omega) hk16 _]
  let u9 := Function.update u8 (rScr ⟨9, by omega⟩) (polBit true (polBit false (u8 (rScr ⟨8, by
      omega⟩)) * polBit false (u8 (rScr ⟨7, by omega⟩))))
  have hi9 : ∀ (k : ℕ) (_ : 9 < k) (hk16 : k < 16) (hk' : k < mScr), u9 (rScr ⟨k, hk'⟩) = 0 :=
    fun k hk hk16 _ ↦ by dsimp only [u9]; rw [Function.update_of_ne (hw_ne k 9 _ _ (by omega)), hi8
        k (by omega) hk16 _]
  let u10 := Function.update u9 (rScr ⟨10, by omega⟩) (polBit true (polBit true (u9 (wSlot0Core
      rCore)) * polBit true (u9 (rScr ⟨3, by omega⟩))))
  have hi10 : ∀ (k : ℕ) (_ : 10 < k) (hk16 : k < 16) (hk' : k < mScr), u10 (rScr ⟨k, hk'⟩) = 0 :=
    fun k hk hk16 _ ↦ by dsimp only [u10]; rw [Function.update_of_ne (hw_ne k 10 _ _ (by omega)),
        hi9 k (by omega) hk16 _]
  let u11 := Function.update u10 (rScr ⟨11, by omega⟩) (polBit false (polBit true (u10 (wSlot2Core
      rCore)) * polBit true (u10 (wSlot1Core rCore))))
  have hi11 : ∀ (k : ℕ) (_ : 11 < k) (hk16 : k < 16) (hk' : k < mScr), u11 (rScr ⟨k, hk'⟩) = 0 :=
    fun k hk hk16 _ ↦ by dsimp only [u11]; rw [Function.update_of_ne (hw_ne k 11 _ _ (by omega)),
        hi10 k (by omega) hk16 _]
  let u12 := Function.update u11 (rScr ⟨12, by omega⟩) (polBit false (polBit true (u11 (wSubReject
      rCore)) * polBit false (u11 (rScr ⟨9, by omega⟩))))
  have hi12 : ∀ (k : ℕ) (_ : 12 < k) (hk16 : k < 16) (hk' : k < mScr), u12 (rScr ⟨k, hk'⟩) = 0 :=
    fun k hk hk16 _ ↦ by dsimp only [u12]; rw [Function.update_of_ne (hw_ne k 12 _ _ (by omega)),
        hi11 k (by omega) hk16 _]
  let u13 := Function.update u12 (rScr ⟨13, by omega⟩) (polBit false (polBit false (u12 (rScr ⟨10,
      by omega⟩)) * polBit false (u12 (wIsHead rCore))))
  have hi13 : ∀ (k : ℕ) (_ : 13 < k) (hk16 : k < 16) (hk' : k < mScr), u13 (rScr ⟨k, hk'⟩) = 0 :=
    fun k hk hk16 _ ↦ by dsimp only [u13]; rw [Function.update_of_ne (hw_ne k 13 _ _ (by omega)),
        hi12 k (by omega) hk16 _]
  let u14 := Function.update u13 (rScr ⟨14, by omega⟩) (polBit false (polBit false (u13 (rScr ⟨11,
      by omega⟩)) * polBit false (u13 (rScr ⟨12, by omega⟩))))
  have cz15 : u14 (rScr ⟨15, by omega⟩) = 0 := by
    dsimp only [u14]; rw [Function.update_of_ne (hw_ne 15 14 _ _ (by decide)), hi13 15 (by decide)
        (by decide) _]
  have hStepFwd : symStepFwdList (origin0HeadEnSteps16 hm16 rCore rScr hCS) β =
      Function.update u14 (rScr ⟨15, by omega⟩)
        (polBit false (polBit false (u14 (rScr ⟨14, by omega⟩)) * polBit false (u14 (rScr ⟨13, by
            omega⟩)))) := by
    dsimp only [origin0HeadEnSteps16]
    rw [symStepFwdList_cons, litAndSymStep_stepFwd _ _ _ _ _ _ _ _ _ β (hc16 0 (by decide) _)]
    change symStepFwdList _ u0 = _
    rw [symStepFwdList_cons, litAndSymStep_stepFwd _ _ _ _ _ _ _ _ _ u0 (hi0 1 (by decide) (by
        decide) _)]
    change symStepFwdList _ u1 = _
    rw [symStepFwdList_cons, litAndSymStep_stepFwd _ _ _ _ _ _ _ _ _ u1 (hi1 2 (by decide) (by
        decide) _)]
    change symStepFwdList _ u2 = _
    rw [symStepFwdList_cons, litAndSymStep_stepFwd _ _ _ _ _ _ _ _ _ u2 (hi2 3 (by decide) (by
        decide) _)]
    change symStepFwdList _ u3 = _
    rw [symStepFwdList_cons, litAndSymStep_stepFwd _ _ _ _ _ _ _ _ _ u3 (hi3 4 (by decide) (by
        decide) _)]
    change symStepFwdList _ u4 = _
    rw [symStepFwdList_cons, litAndSymStep_stepFwd _ _ _ _ _ _ _ _ _ u4 (hi4 5 (by decide) (by
        decide) _)]
    change symStepFwdList _ u5 = _
    rw [symStepFwdList_cons, litAndSymStep_stepFwd _ _ _ _ _ _ _ _ _ u5 (hi5 6 (by decide) (by
        decide) _)]
    change symStepFwdList _ u6 = _
    rw [symStepFwdList_cons, litAndSymStep_stepFwd _ _ _ _ _ _ _ _ _ u6 (hi6 7 (by decide) (by
        decide) _)]
    change symStepFwdList _ u7 = _
    rw [symStepFwdList_cons, litAndSymStep_stepFwd _ _ _ _ _ _ _ _ _ u7 (hi7 8 (by decide) (by
        decide) _)]
    change symStepFwdList _ u8 = _
    rw [symStepFwdList_cons, litAndSymStep_stepFwd _ _ _ _ _ _ _ _ _ u8 (hi8 9 (by decide) (by
        decide) _)]
    change symStepFwdList _ u9 = _
    rw [symStepFwdList_cons, litAndSymStep_stepFwd _ _ _ _ _ _ _ _ _ u9 (hi9 10 (by decide) (by
        decide) _)]
    change symStepFwdList _ u10 = _
    rw [symStepFwdList_cons, litAndSymStep_stepFwd _ _ _ _ _ _ _ _ _ u10 (hi10 11 (by decide) (by
        decide) _)]
    change symStepFwdList _ u11 = _
    rw [symStepFwdList_cons, litAndSymStep_stepFwd _ _ _ _ _ _ _ _ _ u11 (hi11 12 (by decide) (by
        decide) _)]
    change symStepFwdList _ u12 = _
    rw [symStepFwdList_cons, litAndSymStep_stepFwd _ _ _ _ _ _ _ _ _ u12 (hi12 13 (by decide) (by
        decide) _)]
    change symStepFwdList _ u13 = _
    rw [symStepFwdList_cons, litAndSymStep_stepFwd _ _ _ _ _ _ _ _ _ u13 (hi13 14 (by decide) (by
        decide) _)]
    change symStepFwdList _ u14 = _
    rw [symStepFwdList_cons, litAndSymStep_stepFwd _ _ _ _ _ _ _ _ _ u14 cz15]
    rfl
  rw [hStepFwd]
  have hNucW : ∀ i k, x i ≠ rScr k := fun i k ↦ nuc_ne_scr rCore rScr hCS i k
  have hAncW : ∀ i k, y i ≠ rScr k := fun i k ↦ anc_ne_scr rCore rScr hCS i k
  have hs0c : ∀ k, wSlot0Core rCore ≠ rScr k := fun k ↦ wSlot0_ne_scr rCore rScr hCS k
  have hs1c : ∀ k, wSlot1Core rCore ≠ rScr k := fun k ↦ wSlot1_ne_scr rCore rScr hCS k
  have hs2c : ∀ k, wSlot2Core rCore ≠ rScr k := fun k ↦ wSlot2_ne_scr rCore rScr hCS k
  have hsrc : ∀ k, wSubReject rCore ≠ rScr k := fun k ↦ wSubReject_ne_scr rCore rScr hCS k
  have hihc : ∀ k, wIsHead rCore ≠ rScr k := fun k ↦ wIsHead_ne_scr rCore rScr hCS k
  have cu0 : ∀ {c}, (∀ k, c ≠ rScr k) → u0 c = β c := fun hc ↦ by
    dsimp only [u0]; rw [Function.update_of_ne (hc _)]
  have cu1 : ∀ {c}, (∀ k, c ≠ rScr k) → u1 c = β c := fun hc ↦ by
    dsimp only [u1]; rw [Function.update_of_ne (hc _)]; exact cu0 hc
  have cu2 : ∀ {c}, (∀ k, c ≠ rScr k) → u2 c = β c := fun hc ↦ by
    dsimp only [u2]; rw [Function.update_of_ne (hc _)]; exact cu1 hc
  have cu3 : ∀ {c}, (∀ k, c ≠ rScr k) → u3 c = β c := fun hc ↦ by
    dsimp only [u3]; rw [Function.update_of_ne (hc _)]; exact cu2 hc
  have cu4 : ∀ {c}, (∀ k, c ≠ rScr k) → u4 c = β c := fun hc ↦ by
    dsimp only [u4]; rw [Function.update_of_ne (hc _)]; exact cu3 hc
  have cu5 : ∀ {c}, (∀ k, c ≠ rScr k) → u5 c = β c := fun hc ↦ by
    dsimp only [u5]; rw [Function.update_of_ne (hc _)]; exact cu4 hc
  have cu6 : ∀ {c}, (∀ k, c ≠ rScr k) → u6 c = β c := fun hc ↦ by
    dsimp only [u6]; rw [Function.update_of_ne (hc _)]; exact cu5 hc
  have cu7 : ∀ {c}, (∀ k, c ≠ rScr k) → u7 c = β c := fun hc ↦ by
    dsimp only [u7]; rw [Function.update_of_ne (hc _)]; exact cu6 hc
  have cu8 : ∀ {c}, (∀ k, c ≠ rScr k) → u8 c = β c := fun hc ↦ by
    dsimp only [u8]; rw [Function.update_of_ne (hc _)]; exact cu7 hc
  have cu9 : ∀ {c}, (∀ k, c ≠ rScr k) → u9 c = β c := fun hc ↦ by
    dsimp only [u9]; rw [Function.update_of_ne (hc _)]; exact cu8 hc
  have cu10 : ∀ {c}, (∀ k, c ≠ rScr k) → u10 c = β c := fun hc ↦ by
    dsimp only [u10]; rw [Function.update_of_ne (hc _)]; exact cu9 hc
  have cu11 : ∀ {c}, (∀ k, c ≠ rScr k) → u11 c = β c := fun hc ↦ by
    dsimp only [u11]; rw [Function.update_of_ne (hc _)]; exact cu10 hc
  have cu12 : ∀ {c}, (∀ k, c ≠ rScr k) → u12 c = β c := fun hc ↦ by
    dsimp only [u12]; rw [Function.update_of_ne (hc _)]; exact cu11 hc
  constructor
  · intro z hzOut
    have hz_ne : ∀ (k : ℕ) (hk : k < 16) (hk' : k < mScr), z ≠ rScr ⟨k, hk'⟩ := fun k hk _ h ↦
      hzOut (QRegister.mem_image _ z |>.mpr ⟨⟨k, hk⟩,
        (congrArg rScr.wires (Fin.ext (by dsimp [QRegister.slice_apply]; omega))).trans h.symm⟩)
    rw [Function.update_of_ne (hz_ne 15 (by decide) _)]
    dsimp only [u14]; rw [Function.update_of_ne (hz_ne 14 (by decide) _)]
    dsimp only [u13]; rw [Function.update_of_ne (hz_ne 13 (by decide) _)]
    dsimp only [u12]; rw [Function.update_of_ne (hz_ne 12 (by decide) _)]
    dsimp only [u11]; rw [Function.update_of_ne (hz_ne 11 (by decide) _)]
    dsimp only [u10]; rw [Function.update_of_ne (hz_ne 10 (by decide) _)]
    dsimp only [u9]; rw [Function.update_of_ne (hz_ne 9 (by decide) _)]
    dsimp only [u8]; rw [Function.update_of_ne (hz_ne 8 (by decide) _)]
    dsimp only [u7]; rw [Function.update_of_ne (hz_ne 7 (by decide) _)]
    dsimp only [u6]; rw [Function.update_of_ne (hz_ne 6 (by decide) _)]
    dsimp only [u5]; rw [Function.update_of_ne (hz_ne 5 (by decide) _)]
    dsimp only [u4]; rw [Function.update_of_ne (hz_ne 4 (by decide) _)]
    dsimp only [u3]; rw [Function.update_of_ne (hz_ne 3 (by decide) _)]
    dsimp only [u2]; rw [Function.update_of_ne (hz_ne 2 (by decide) _)]
    dsimp only [u1]; rw [Function.update_of_ne (hz_ne 1 (by decide) _)]
    dsimp only [u0]; rw [Function.update_of_ne (hz_ne 0 (by decide) _)]
  · have v0 : u0 (rScr ⟨0, by omega⟩) = polBit false (polBit false (β (x 4)) * polBit false (β (x
      3))) := by
      dsimp only [u0]; rw [Function.update_self]
    have v1 : u2 (rScr ⟨1, by omega⟩) = polBit true (polBit true (β (x 5)) * polBit true (u0 (rScr
        ⟨0, by omega⟩))) := by
      dsimp only [u2]; rw [Function.update_of_ne (hw_ne 1 2 _ _ (by decide))]
      dsimp only [u1]; rw [Function.update_self, cu0 (hNucW 5)]
    have v2 : u2 (rScr ⟨2, by omega⟩) = polBit false (polBit false (β (x 7)) * polBit false (β (x
        6))) := by
      dsimp only [u2]; rw [Function.update_self, cu1 (hNucW 7), cu1 (hNucW 6)]
    have v3_raw : u3 (rScr ⟨3, by omega⟩) = if decide (regVal (rNucIdx rCore) β < 216) then 1 else
        0 := by
      dsimp only [u3]; rw [Function.update_self, v2, v1, v0]
      have h := phcHead_polBit_lt216_decide (β (x 0)) (β (x 1)) (β (x 2)) (β (x 3))
        (β (x 4)) (β (x 5)) (β (x 6)) (β (x 7))
      rw [← regVal8_expand x β] at h
      exact h
    have v3 : u9 (rScr ⟨3, by omega⟩) = if decide (regVal (rNucIdx rCore) β < 216) then 1 else 0 :=
        by
      dsimp only [u9]; rw [Function.update_of_ne (hw_ne 3 9 _ _ (by decide))]
      dsimp only [u8]; rw [Function.update_of_ne (hw_ne 3 8 _ _ (by decide))]
      dsimp only [u7]; rw [Function.update_of_ne (hw_ne 3 7 _ _ (by decide))]
      dsimp only [u6]; rw [Function.update_of_ne (hw_ne 3 6 _ _ (by decide))]
      dsimp only [u5]; rw [Function.update_of_ne (hw_ne 3 5 _ _ (by decide))]
      dsimp only [u4]; rw [Function.update_of_ne (hw_ne 3 4 _ _ (by decide)), v3_raw]
    have v4 : u5 (rScr ⟨4, by omega⟩) = polBit true (polBit true (β (y 2)) * polBit true (β (y 1)))
        := by
      dsimp only [u5]; rw [Function.update_of_ne (hw_ne 4 5 _ _ (by decide))]
      dsimp only [u4]; rw [Function.update_self, cu3 (hAncW 2), cu3 (hAncW 1)]
    have v5 : u5 (rScr ⟨5, by omega⟩) = polBit false (polBit false (β (y 4)) * polBit false (β (y
        3))) := by
      dsimp only [u5]; rw [Function.update_self, cu4 (hAncW 4), cu4 (hAncW 3)]
    have v6 : u6 (rScr ⟨6, by omega⟩) = polBit false (polBit false (u5 (rScr ⟨5, by omega⟩)) *
        polBit false (u5 (rScr ⟨4, by omega⟩))) := by
      dsimp only [u6]; rw [Function.update_self]
    have v7 : u8 (rScr ⟨7, by omega⟩) = polBit true (polBit true (β (y 5)) * polBit true (u6 (rScr
        ⟨6, by omega⟩))) := by
      dsimp only [u8]; rw [Function.update_of_ne (hw_ne 7 8 _ _ (by decide))]
      dsimp only [u7]; rw [Function.update_self, cu6 (hAncW 5)]
    have v8 : u8 (rScr ⟨8, by omega⟩) = polBit false (polBit false (β (y 7)) * polBit false (β (y
        6))) := by
      dsimp only [u8]; rw [Function.update_self, cu7 (hAncW 7), cu7 (hAncW 6)]
    have v9_raw : u9 (rScr ⟨9, by omega⟩) = if decide (regVal (rAnchorIdx rCore) β < 218) then 1
        else 0 := by
      dsimp only [u9]; rw [Function.update_self, v8, v7, v6, v5, v4]
      have h := phcHead_polBit_lt218_decide (β (y 0)) (β (y 1)) (β (y 2)) (β (y 3))
        (β (y 4)) (β (y 5)) (β (y 6)) (β (y 7))
      rw [← regVal8_expand y β] at h
      exact h
    have v9 : u11 (rScr ⟨9, by omega⟩) = if decide (regVal (rAnchorIdx rCore) β < 218) then 1 else
        0 := by
      dsimp only [u11]; rw [Function.update_of_ne (hw_ne 9 11 _ _ (by decide))]
      dsimp only [u10]; rw [Function.update_of_ne (hw_ne 9 10 _ _ (by decide)), v9_raw]
    have v10 : u12 (rScr ⟨10, by omega⟩) = polBit true (polBit true (β (wSlot0Core rCore)) *
        polBit true (if decide (regVal (rNucIdx rCore) β < 216) then 1 else 0)) := by
      dsimp only [u12]; rw [Function.update_of_ne (hw_ne 10 12 _ _ (by decide))]
      dsimp only [u11]; rw [Function.update_of_ne (hw_ne 10 11 _ _ (by decide))]
      dsimp only [u10]; rw [Function.update_self, cu9 hs0c, v3]
    have v11 : u13 (rScr ⟨11, by omega⟩) =
        polBit false (polBit true (β (wSlot2Core rCore)) * polBit true (β (wSlot1Core rCore))) := by
      dsimp only [u13]; rw [Function.update_of_ne (hw_ne 11 13 _ _ (by decide))]
      dsimp only [u12]; rw [Function.update_of_ne (hw_ne 11 12 _ _ (by decide))]
      dsimp only [u11]; rw [Function.update_self, cu10 hs2c, cu10 hs1c]
    have v12 : u13 (rScr ⟨12, by omega⟩) = polBit false (polBit true (β (wSubReject rCore)) *
        polBit false (if decide (regVal (rAnchorIdx rCore) β < 218) then 1 else 0)) := by
      dsimp only [u13]; rw [Function.update_of_ne (hw_ne 12 13 _ _ (by decide))]
      dsimp only [u12]; rw [Function.update_self, cu11 hsrc, v9]
    have v13 : u14 (rScr ⟨13, by omega⟩) =
        polBit false (polBit false (u12 (rScr ⟨10, by omega⟩)) * polBit false (β (wIsHead rCore)))
            := by
      dsimp only [u14]; rw [Function.update_of_ne (hw_ne 13 14 _ _ (by decide))]
      dsimp only [u13]; rw [Function.update_self, cu12 hihc]
    have v14 : u14 (rScr ⟨14, by omega⟩) =
        polBit false (polBit false (u13 (rScr ⟨11, by omega⟩)) * polBit false (u13 (rScr ⟨12, by
            omega⟩))) := by
      dsimp only [u14]; rw [Function.update_self]
    rw [Function.update_self, v14, v13, v12, v11, v10]
    exact polBit_headEnBoolSpec_eq rCore β
theorem headEnBoolSpec_zeroSlot0Bits (β : BitAssignment posCoreWires) :
    headEnBoolSpec (zeroSlot0Bits β) = headEnBoolSpec β := by
  let rCore := QRegExt.ofFin posCoreWires
  have hS2 : zeroSlot0Bits β (wSlot2Core rCore) = β (wSlot2Core rCore) := rfl
  have hS1 : zeroSlot0Bits β (wSlot1Core rCore) = β (wSlot1Core rCore) := rfl
  have hS0 : zeroSlot0Bits β (wSlot0Core rCore) = β (wSlot0Core rCore) := rfl
  have hSR : zeroSlot0Bits β (wSubReject rCore) = β (wSubReject rCore) := rfl
  have hIH : zeroSlot0Bits β (wIsHead rCore) = β (wIsHead rCore) := rfl
  have hNuc : regVal (rNucIdx rCore) (zeroSlot0Bits β) = regVal (rNucIdx rCore) β := by
    unfold regVal bitsVal
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hi : ¬ ((rNucIdx rCore i).val < 18) := by
      revert i; decide
    dsimp only [zeroSlot0Bits]
    rw [ite_eq_right hi]
  have hAnc : regVal (rAnchorIdx rCore) (zeroSlot0Bits β) = regVal (rAnchorIdx rCore) β := by
    unfold regVal bitsVal
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hi : ¬ ((rAnchorIdx rCore i).val < 18) := by
      revert i; decide
    dsimp only [zeroSlot0Bits]
    rw [ite_eq_right hi]
  dsimp only [headEnBoolSpec]
  dsimp only [rCore] at hS2 hS1 hS0 hSR hIH hNuc hAnc
  rw [hS2, hS1, hS0, hSR, hIH, hNuc, hAnc]
end Part1_Origin0Head34Realizes
end Origin0Head34RealizesAndLeaf2Spec
end XorForestStageABody
namespace PartnerAndAnchorSlot18LensAndMidBA
section Impl02n
set_option maxRecDepth 65536
open HermitianMat
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens)
/-- Replacing a subregister `r` with `r.extractIndex d` returns `d`. -/
@[simp] theorem replaceIndex_extractIndex {n k : ℕ} (r : QRegister k n) (d : Fin (2 ^ n)) :
    r.replaceIndex d (r.extractIndex d) = d := by
  apply (basisBitsEquiv n).injective
  funext w
  change basisBits n (r.replaceIndex d (r.extractIndex d)) w = basisBits n d w
  by_cases hw : w ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hw
    rw [QRegister.basisBits_replaceIndex_apply, QRegister.basisBits_extractIndex]
  · exact QRegister.basisBits_replaceIndex_of_not_mem r d (r.extractIndex d) w hw
/-- Replacing a subregister `r` twice keeps the second value `v₂`. -/
@[simp] theorem replaceIndex_replaceIndex {n k : ℕ} (r : QRegister k n)
    (d : Fin (2 ^ n)) (v₁ v₂ : Fin (2 ^ k)) :
    r.replaceIndex (r.replaceIndex d v₁) v₂ = r.replaceIndex d v₂ := by
  apply (basisBitsEquiv n).injective
  funext w
  change basisBits n (r.replaceIndex (r.replaceIndex d v₁) v₂) w =
    basisBits n (r.replaceIndex d v₂) w
  by_cases hw : w ∈ Set.range r.wires
  · obtain ⟨i, rfl⟩ := hw
    rw [QRegister.basisBits_replaceIndex_apply, QRegister.basisBits_replaceIndex_apply]
  · rw [QRegister.basisBits_replaceIndex_of_not_mem r _ v₂ w hw,
        QRegister.basisBits_replaceIndex_of_not_mem r d v₁ w hw,
        QRegister.basisBits_replaceIndex_of_not_mem r d v₂ w hw]
/-- **General Indexed-Slot `Slot18Lens` Constructor (`mkSlot18LensOfSlotReg`)**:
For any state-dependent 18-wire slot selector `slotOf : Fin (2 ^ kData) → QRegister 18 kData`
whose selected slot is invariant under writing to `slotOf d`
(`∀ d v, slotOf ((slotOf d).replaceIndex d v) = slotOf d`),
`(tbl d := (slotOf d).extractIndex d, updSlot d v := (slotOf d).replaceIndex d v)` is a `Slot18Lens
kData`! -/
noncomputable def mkSlot18LensOfSlotReg {kData : ℕ}
    (slotOf : Fin (2 ^ kData) → QRegister 18 kData)
    (hSlotInv : ∀ (d : Fin (2 ^ kData)) (v : Fin (2 ^ 18)),
      slotOf ((slotOf d).replaceIndex d v) = slotOf d) :
    Slot18Lens kData where
  tbl d := (slotOf d).extractIndex d
  updSlot d v := (slotOf d).replaceIndex d v
  get_put d v := by
    rw [hSlotInv d v, QRegister.extractIndex_replaceIndex]
  put_get d := replaceIndex_extractIndex (slotOf d) d
  put_put d v₁ v₂ := by
    rw [hSlotInv d v₁, replaceIndex_replaceIndex]
/-- **Subregister `Slot18Lens` Lifter (`liftSlot18Lens`)**:
Lifts any `L : Slot18Lens k₁` along `sel : QRegister k₁ k₂` to a `Slot18Lens k₂` with
`tbl x = L.tbl (sel.extractIndex x)` and `updSlot x v = sel.replaceIndex x (L.updSlot
(sel.extractIndex x) v)`! -/
noncomputable def liftSlot18Lens {k₁ k₂ : ℕ}
    (sel : QRegister k₁ k₂) (L : Slot18Lens k₁) : Slot18Lens k₂ where
  tbl x := L.tbl (sel.extractIndex x)
  updSlot x v := sel.replaceIndex x (L.updSlot (sel.extractIndex x) v)
  get_put x v := by
    rw [sel.extractIndex_replaceIndex, L.get_put]
  put_get x := by
    rw [L.put_get, replaceIndex_extractIndex]
  put_put x v₁ v₂ := by
    rw [sel.extractIndex_replaceIndex, replaceIndex_replaceIndex, L.put_put]
end Impl02n
end PartnerAndAnchorSlot18LensAndMidBA
set_option maxRecDepth 65536
namespace ElecHadTrueSwapLocalCompClosure
section ImplElecHad
open HermitianMat
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open BchCubeDecoder
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens lensSwapPerm
  lensSwapPerm_involutive)
/-- Pair extractor `extractPair g := ((selDataInAct kData).extractIndex g, (selMeasInAct
  kData).extractIndex g)`
splitting `Fin (2 ^ (kData + 18))` into data index `Fin (2 ^ kData)` and 18-bit ancilla index `Fin
(2 ^ 18)`. -/
def extractPair {kData : ℕ} (g : Fin (2 ^ (kData + 18))) : Fin (2 ^ kData) × Fin (2 ^ 18) :=
  ((selDataInAct kData).extractIndex g, (selMeasInAct kData).extractIndex g)
/-- Lifts any map `F : Fin (2 ^ kData) × Fin (2 ^ 18) → Fin (2 ^ kData) × Fin (2 ^ 18)`
to `Fin (2 ^ (kData + 18)) → Fin (2 ^ (kData + 18))` via `selDataInAct` and `selMeasInAct`. -/
noncomputable def liftPairIdx {kData : ℕ} (F : Fin (2 ^ kData) × Fin (2 ^ 18) → Fin (2 ^
    kData) × Fin (2 ^ 18)) (g : Fin (2 ^ (kData + 18))) : Fin (2 ^ (kData + 18)) :=
  let p := F (extractPair g)
  (selMeasInAct kData).replaceIndex ((selDataInAct kData).replaceIndex g p.1) p.2
@[simp] theorem extractPair_liftPairIdx {kData : ℕ} (F : Fin (2 ^ kData) × Fin (2 ^ 18) → Fin
    (2 ^ kData) × Fin (2 ^ 18)) (g : Fin (2 ^ (kData + 18))) : extractPair (liftPairIdx F g) =
    F (extractPair g) := by
  dsimp only [extractPair, liftPairIdx]
  ext
  · rw [QRegister.extractIndex_replaceIndex_of_disjoint
        (selDataInAct kData) (selMeasInAct kData) (selDataInAct_disj_selMeasInAct kData),
      QRegister.extractIndex_replaceIndex]
  · rw [QRegister.extractIndex_replaceIndex]
@[simp] theorem liftPairIdx_comp {kData : ℕ} (G F : Fin (2 ^ kData) × Fin (2 ^ 18) → Fin (2 ^
    kData) × Fin (2 ^ 18)) (g : Fin (2 ^ (kData + 18))) : liftPairIdx G (liftPairIdx F g) =
    liftPairIdx (fun p ↦ G (F p)) g := by
  have hEx : extractPair ((selMeasInAct kData).replaceIndex ((selDataInAct kData).replaceIndex
      g (F (extractPair g)).1) (F (extractPair g)).2) = F (extractPair g) :=
      extractPair_liftPairIdx F g
  dsimp only [liftPairIdx]
  rw [hEx,
      QRegister.replaceIndex_comm_of_disjoint
        (selDataInAct kData) (selMeasInAct kData) (selDataInAct_disj_selMeasInAct kData),
      QRegister.replaceIndex_replaceIndex,
      QRegister.replaceIndex_replaceIndex]
@[simp] theorem liftPairIdx_id {kData : ℕ} (g : Fin (2 ^ (kData + 18))) :
    liftPairIdx id g = g := by
  dsimp only [liftPairIdx, extractPair, id]
  rw [QRegister.replaceIndex_extractIndex, QRegister.replaceIndex_extractIndex]
theorem liftPairIdx_involutive {kData : ℕ}
    {F : Fin (2 ^ kData) × Fin (2 ^ 18) → Fin (2 ^ kData) × Fin (2 ^ 18)}
    (hF : Function.Involutive F) :
    Function.Involutive (liftPairIdx F) := fun g ↦ by
  rw [liftPairIdx_comp]
  have hId : (fun p ↦ F (F p)) = id := funext hF
  rw [hId, liftPairIdx_id]
/-- Permutation equivalence on `Fin (2 ^ (kData + 18))` induced by `lensSwapPerm L`. -/
noncomputable def lensSwapEquiv {kData : ℕ} (L : Slot18Lens kData) : Equiv.Perm
    (Fin (2 ^ (kData + 18))) := Equiv.ofBijective (liftPairIdx (lensSwapPerm L))
    (liftPairIdx_involutive (lensSwapPerm_involutive L)).bijective
/-- Unitary `uLensSwap L : Unitary (2 ^ (kData + 18))` for `lensSwapPerm L`. -/
noncomputable def uLensSwap {kData : ℕ} (L : Slot18Lens kData) : Unitary (2 ^ (kData + 18)) :=
    Operator.permutationUnitary (lensSwapEquiv L)
end ImplElecHad
end ElecHadTrueSwapLocalCompClosure
namespace ZeroHypSlot0CommAndHMidClosure
section Impl10f
open HermitianMat
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open PosSlots24Barrel3Pass (permUnitary_apply)
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens lensSwapPerm
  lensSwapPerm_involutive)
open ElecHadTrueSwapLocalCompClosure (extractPair_liftPairIdx
  liftPairIdx_involutive lensSwapEquiv uLensSwap)
theorem basisOutcomeProjector_zero_mul_self {n k : ℕ} (r : QRegister k n) :
    r.basisOutcomeProjector 0 * r.basisOutcomeProjector 0 = r.basisOutcomeProjector 0 := by
  ext i j
  simp only [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hz : r.extractIndex i = 0 <;> simp [hz]
  · simp [hij]
theorem lensSwapEquiv_involutive {kData : ℕ} (L : Slot18Lens kData) : Function.Involutive
    (lensSwapEquiv L) := liftPairIdx_involutive (lensSwapPerm_involutive L)
theorem lensSwapEquiv_mul_self {kData : ℕ} (L : Slot18Lens kData) :
    lensSwapEquiv L * lensSwapEquiv L = 1 := by
  ext g
  exact congrArg Fin.val (lensSwapEquiv_involutive L g)
@[simp] theorem uLensSwap_mul_self {kData : ℕ} (L : Slot18Lens kData) :
    uLensSwap L * uLensSwap L = 1 := by
  dsimp only [uLensSwap]
  rw [← OperatorExt.permutationUnitary_mul, lensSwapEquiv_mul_self,
    OperatorExt.permutationUnitary_one]
@[simp] theorem uLensSwap_val_mul_self {kData : ℕ} (L : Slot18Lens kData) :
    (uLensSwap L).1 * (uLensSwap L).1 = 1 := by
  rw [← Submonoid.coe_mul, uLensSwap_mul_self, Submonoid.coe_one]
@[simp] theorem uLensSwap_inv {kData : ℕ} (L : Slot18Lens kData) : (uLensSwap L)⁻¹ = uLensSwap
    L := inv_eq_iff_mul_eq_one.mpr (uLensSwap_mul_self L)
/-- Matrix entry of `(uLensSwap L).1 * A * (uLensSwap L).1`. -/
theorem uLensSwap_conj_apply {kData : ℕ} (L : Slot18Lens kData)
    (A : Operator (2 ^ (kData + 18))) (i j : Fin (2 ^ (kData + 18))) :
    ((uLensSwap L).1 * A * (uLensSwap L).1) i j =
      A (lensSwapEquiv L i) (lensSwapEquiv L j) := by
  have hRight : ∀ (B : Operator (2 ^ (kData + 18))) (r c : Fin (2 ^ (kData + 18))),
      (B * (uLensSwap L).1) r c = B r (lensSwapEquiv L c) := fun B r c ↦ by
    rw [Matrix.mul_apply, Finset.sum_eq_single (lensSwapEquiv L c)]
    · dsimp only [uLensSwap]
      rw [permUnitary_apply, ite_eq_left rfl, mul_one]
    · intro k _ hk
      dsimp only [uLensSwap]
      rw [permUnitary_apply, ite_eq_right hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hLeft : ∀ (r c : Fin (2 ^ (kData + 18))),
      ((uLensSwap L).1 * A) r c = A (lensSwapEquiv L r) c := fun r c ↦ by
    rw [Matrix.mul_apply, Finset.sum_eq_single (lensSwapEquiv L r)]
    · dsimp only [uLensSwap]
      have hInv : r = lensSwapEquiv L (lensSwapEquiv L r) := (lensSwapEquiv_involutive L r).symm
      rw [permUnitary_apply, ite_eq_left hInv, one_mul]
    · intro m _ hm
      dsimp only [uLensSwap]
      have hne : r ≠ lensSwapEquiv L m := fun hr ↦ hm (by rw [hr, lensSwapEquiv_involutive L m])
      rw [permUnitary_apply, ite_eq_right hne, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hRight ((uLensSwap L).1 * A) i j, hLeft i (lensSwapEquiv L j)]
@[simp] theorem selMeasInAct_extractIndex_lensSwapEquiv {kData : ℕ} (L : Slot18Lens kData)
    (xy : Fin (2 ^ (kData + 18))) : (selMeasInAct kData).extractIndex (lensSwapEquiv L xy) =
    L.tbl ((selDataInAct kData).extractIndex xy) := by
  have h := congrArg Prod.snd (extractPair_liftPairIdx (lensSwapPerm L) xy)
  exact h
/-- **Active-Slot Zero Projector (`P_slot0 L`)**:
Conjugates `Pm = (selMeasInAct kData).basisOutcomeProjector 0` by `uLensSwap L`, projecting onto
the subspace where the active electron slot `L.tbl ((selDataInAct kData).extractIndex xy)` is
`|0^{18}⟩`. -/
noncomputable def P_slot0 {kData : ℕ} (L : Slot18Lens kData) : Operator (2 ^ (kData + 18)) :=
  (uLensSwap L).1 * (selMeasInAct kData).basisOutcomeProjector 0 * (uLensSwap L).1
/-- **Explicit Diagonal Form of `P_slot0 L` (`P_slot0_eq_diagonal`)**:
`P_slot0 L = Matrix.diagonal (fun xy ↦ if L.tbl ((selDataInAct kData).extractIndex xy) = 0 then (1
: ℂ) else 0)`. -/
theorem P_slot0_eq_diagonal {kData : ℕ} (L : Slot18Lens kData) : P_slot0 L = Matrix.diagonal
    (fun xy ↦ if L.tbl ((selDataInAct kData).extractIndex xy) = 0 then (1 : ℂ) else 0) := by
  ext i j
  dsimp only [P_slot0]
  rw [uLensSwap_conj_apply, QRegister.basisOutcomeProjector_eq_diagonal]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.diagonal_apply_eq, selMeasInAct_extractIndex_lensSwapEquiv]
  · have hne : lensSwapEquiv L i ≠ lensSwapEquiv L j :=
      fun h ↦ hij ((lensSwapEquiv L).injective h)
    rw [Matrix.diagonal_apply_ne _ hne, Matrix.diagonal_apply_ne _ hij]
end Impl10f
end ZeroHypSlot0CommAndHMidClosure
namespace PureCnotLensLoadAndZeroHypTrueSwap
section ImplAux
open HermitianMat
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens lensSwapPerm_involutive)
open ElecHadTrueSwapLocalCompClosure (liftPairIdx_involutive lensSwapEquiv
  uLensSwap)
/-- **Unconditional Self-Involutivity of `uLensSwap L` (`uLensSwap_mul_self_eq_one`)**. -/
@[simp] theorem uLensSwap_mul_self_eq_one {kData : ℕ} (L : Slot18Lens kData) :
    uLensSwap L * uLensSwap L = 1 := by
  dsimp only [uLensSwap]
  rw [← OperatorExt.permutationUnitary_mul]
  have hInv : lensSwapEquiv L * lensSwapEquiv L = 1 :=
    Equiv.ext fun g ↦ liftPairIdx_involutive (lensSwapPerm_involutive L) g
  rw [hInv, OperatorExt.permutationUnitary_one]
end ImplAux
end PureCnotLensLoadAndZeroHypTrueSwap
namespace ZeroHypHMidBAndPureCnotSwapClosure
section Impl08g
open HermitianMat
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open PosSlots24Barrel3Pass (permUnitary_apply)
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens lensSwapPerm_involutive)
open ElecHadTrueSwapLocalCompClosure (liftPairIdx_involutive lensSwapEquiv
  uLensSwap)
theorem lensSwapEquiv_involutive {kData : ℕ} (L : Slot18Lens kData)
    (g : Fin (2 ^ (kData + 18))) : lensSwapEquiv L (lensSwapEquiv L g) = g :=
    liftPairIdx_involutive (lensSwapPerm_involutive L) g
theorem uLensSwap_apply {kData : ℕ} (L : Slot18Lens kData) (i j : Fin (2 ^ (kData + 18))) :
    (uLensSwap L).1 i j = if i = lensSwapEquiv L j then 1 else 0 := permUnitary_apply
    (lensSwapEquiv L) i j
@[simp] theorem uLensSwap_val_mul_self {kData : ℕ} (L : Slot18Lens kData) :
    (uLensSwap L).1 * (uLensSwap L).1 = 1 := by
  ext i j
  simp only [Matrix.mul_apply, uLensSwap_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (lensSwapEquiv L j)]
  · rw [ite_eq_left rfl, mul_one]
    have hiff : i = lensSwapEquiv L (lensSwapEquiv L j) ↔ i = j := by
      rw [lensSwapEquiv_involutive L j]
    rw [if_congr hiff rfl rfl]
  · intro k _ hkj
    rw [ite_eq_right hkj, mul_zero]
  · intro h
    exact False.elim (h (Finset.mem_univ _))
@[simp] theorem uLensSwap_mul_self {kData : ℕ} (L : Slot18Lens kData) : uLensSwap L *
    uLensSwap L = 1 := Subtype.ext (uLensSwap_val_mul_self L)
/-- **Embedding a Diagonal Matrix via `QRegister.embedMatrix` Yields a Diagonal Matrix
(`embedMatrix_diagonal_eq`)**:
For any subregister `r : QRegister k m` and diagonal entries `d0 : Fin (2 ^ k) → ℂ`,
`r.embedMatrix (Matrix.diagonal d0) = Matrix.diagonal (fun xy ↦ d0 (r.extractIndex xy))`! -/
theorem embedMatrix_diagonal_eq {m k : ℕ} (r : QRegister k m) (d0 : Fin (2 ^ k) → ℂ) :
    r.embedMatrix (Matrix.diagonal d0) = Matrix.diagonal (fun xy ↦ d0 (r.extractIndex xy)) := by
  ext i g
  rw [QRegister.embedMatrix_apply]
  by_cases hig : i = g
  · subst hig
    simp [Matrix.diagonal]
  · rw [Matrix.diagonal_apply_ne _ hig]
    by_cases hEx : r.extractIndex i = r.extractIndex g
    · have hEnv : (r.basisSplitEquiv i).2 ≠ (r.basisSplitEquiv g).2 := by
        intro h2
        apply hig
        have h1 : (r.basisSplitEquiv i).1 = (r.basisSplitEquiv g).1 := by
          rw [QRegister.basisSplitEquiv_apply_fst, QRegister.basisSplitEquiv_apply_fst, hEx]
        exact r.basisSplitEquiv.injective (Prod.ext h1 h2)
      rw [ite_eq_right hEnv, mul_zero]
    · rw [Matrix.diagonal_apply_ne _ hEx, zero_mul]
end Impl08g
end ZeroHypHMidBAndPureCnotSwapClosure
namespace ZeroHypStageBPureCnotAndHMidBClosure
section Impl08b
open HermitianMat
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
/-- Axis wire map `idxForestAx18 (l : Fin 3) (q : Fin 6) : Fin 18` for `xorForestBatch_spec` at
  `kSys = 18`. -/
def idxForestAx18 (l : Fin 3) (q : Fin 6) : Fin 18 :=
  ⟨6 * l.val + q.val, by have := l.isLt; have := q.isLt; omega⟩
theorem idxForestAx18_inj :
    Function.Injective (fun p : Fin 3 × Fin 6 ↦ idxForestAx18 p.1 p.2) := by
  intro ⟨l₁, q₁⟩ ⟨l₂, q₂⟩ h
  have hv := congrArg Fin.val h
  dsimp only [idxForestAx18] at hv
  have hl : l₁.val = l₂.val := by have := q₁.isLt; have := q₂.isLt; omega
  have hq : q₁.val = q₂.val := by omega
  exact Prod.ext (Fin.ext hl) (Fin.ext hq)
end Impl08b
end ZeroHypStageBPureCnotAndHMidBClosure
set_option exponentiation.threshold 8192
namespace MasterZeroHypCompactAndCompactTopBridge
open HermitianMat
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open SpecsAux SpecsAux.SpecMirror
open InterWalkRSum42Hoist (qreg_ext)
open DyadicQft64WalkCircuit (rIdInCat rPGInCat disjoint_block_sep)
open CoreQftHadamard140And160 (rQftCanon128 rSysCanon128 rPGCanon128
  rSysCanon128_disjoint_rPGCanon128)
section Part1_ZeroHypStageBQftAndSlot0Comm
/-- For any disjoint `rAct : QRegister k n` and `rWork : QRegister m n`,
`A ↦ rAct.embedMatrix A * rWork.basisOutcomeProjector 0` is injective. -/
theorem embedMatrix_inj_on_work_zero {n k m : ℕ} (rAct : QRegister k n)
    (rWork : QRegister m n) (hDisj : rAct.DisjointWires rWork) {A B : Operator (2 ^ k)} (h :
    rAct.embedMatrix A * rWork.basisOutcomeProjector 0 = rAct.embedMatrix B *
    rWork.basisOutcomeProjector 0) : A = B := by
  ext x y
  let z₀ : Fin (2 ^ n) := rWork.replaceIndex 0 0
  let i : Fin (2 ^ n) := rAct.replaceIndex z₀ x
  let j : Fin (2 ^ n) := rAct.replaceIndex z₀ y
  have hij := congrFun (congrFun h i) j
  have hj0 : rWork.extractIndex j = 0 := by
    dsimp only [j, z₀]
    rw
      [QRegister.extractIndex_replaceIndex_of_disjoint rWork rAct
      (QRegExt.disjointWires_symm hDisj),
        QRegister.extractIndex_replaceIndex]
  have henv : (rAct.basisSplitEquiv i).2 = (rAct.basisSplitEquiv j).2 := by
    dsimp only [i, j]
    rw [rAct.basisSplitEquiv_replaceIndex, rAct.basisSplitEquiv_replaceIndex]
  have hx : rAct.extractIndex i = x := rAct.extractIndex_replaceIndex z₀ x
  have hy : rAct.extractIndex j = y := rAct.extractIndex_replaceIndex z₀ y
  rw[QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal, Matrix.mul_diagonal,
      ite_eq_left hj0, mul_one, mul_one, QRegister.embedMatrix_apply, QRegister.embedMatrix_apply,
      ite_eq_left henv, hx, hy, mul_one, mul_one] at hij
  exact hij
def sel18InSys : QRegister 18 (3924 + 3) where
  wires := ⟨fun i ↦ ⟨i.val, by have := i.isLt; omega⟩,
    by intro i j h; have hv := congrArg Fin.val h; exact Fin.ext hv⟩
theorem rIdInCat_disj_rPGInCat : rIdInCat.DisjointWires rPGInCat :=
  disjoint_block_sep (by decide)
def sel25InCat : QRegister (18 + 7) (3924 + 3 + 7) := (rIdInCat.compose sel18InSys).concat
    rPGInCat (rIdInCat_disj_rPGInCat.compose_left sel18InSys)
theorem concat_sel18InSys_rPGCanon128_eq : (rSysCanon128.compose sel18InSys).concat
    rPGCanon128 (rSysCanon128_disjoint_rPGCanon128.compose_left sel18InSys) =
    rQftCanon128.compose sel25InCat := by
  apply qreg_ext; intro idx
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) idx
  · change ((rSysCanon128.compose sel18InSys).concat rPGCanon128 _) (Fin.castAdd 7 i) =
      rQftCanon128 (sel25InCat (Fin.castAdd 7 i))
    rw [QRegister.concat_apply_left, sel25InCat, QRegister.concat_apply_left]
    rfl
  · change ((rSysCanon128.compose sel18InSys).concat rPGCanon128 _) (Fin.natAdd 18 j) =
      rQftCanon128 (sel25InCat (Fin.natAdd 18 j))
    rw [QRegister.concat_apply_right, sel25InCat, QRegister.concat_apply_right]
    rfl
end Part1_ZeroHypStageBQftAndSlot0Comm
export ZeroHypSlot0CommAndHMidClosure (P_slot0 P_slot0_eq_diagonal)
end MasterZeroHypCompactAndCompactTopBridge
section ScopeBoothOpt
namespace BoothOpt_03_CoinBarrelIdxFastTrueSwap
section ImplBoothOpt_03
set_option exponentiation.threshold 256
set_option backward.isDefEq.respectTransparency false
open HermitianMat
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open FullSysCatSegmentBridge (fullSysCoreWires)
open CoinDispatchedBarrel288 (coinBarrelIdxFast coinBarrelIdxFast_congr_high)
open PosSlots24BranchConcrete (posCoreWires rElecSlot)
open PosSlots24SemanticBridge (pos24_coreWires80_eq)
open PosSlots24PartnerMux288 (eq_of_basisBits_eq)
open ElecHadConjLoadAndTrueSwapComp (Slot18Lens)
open ElecHadTrueSwapHCompClosure (h3924_le_posCoreWires)
open PartnerAndAnchorSlot18LensAndMidBA (mkSlot18LensOfSlotReg liftSlot18Lens)
/-- Support predicate: `z` agrees with `g₀` on every wire outside `S`. -/
def SameOutside {N : ℕ} (S : Set (Wire N)) (g₀ z : Fin (2 ^ N)) : Prop :=
  ∀ w ∉ S, basisBits N z w = basisBits N g₀ w
theorem posCoreWires_le_fullSysCoreWires {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    posCoreWires ≤ fullSysCoreWires mPayload := by
  rw [← pos24_coreWires80_eq]
  dsimp [fullSysCoreWires]
  omega
theorem h3924_le_fullSysCoreWires {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    3924 ≤ fullSysCoreWires mPayload :=
  le_trans h3924_le_posCoreWires (posCoreWires_le_fullSysCoreWires hmPay)
/-- Prefix selector `selPosInFullSys hmPay : QRegister posCoreWires (fullSysCoreWires mPayload)`
embedding the first `posCoreWires = 4,034` wires (`including [0..3924) and rAnchorIdx =
[3968..3976)`)
inside `fullSysCoreWires mPayload`. -/
def selPosInFullSys {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    QRegister posCoreWires (fullSysCoreWires mPayload) :=
  (QRegExt.ofFin (fullSysCoreWires mPayload)).slice 0 posCoreWires
    (by have := posCoreWires_le_fullSysCoreWires hmPay; omega)
theorem selPosInFullSys_val {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (i : Fin posCoreWires) :
    (selPosInFullSys hmPay i).val = i.val := by
  simp [selPosInFullSys, QRegister.slice, QRegExt.ofFin]
/-- `18`-wire electron slot `e : Fin 218` inside `fullSysCoreWires mPayload`. -/
def rFullSysElecSlot {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (e : Fin 218) :
    QRegister 18 (fullSysCoreWires mPayload) :=
  (selPosInFullSys hmPay).compose (rElecSlot (QRegExt.ofFin posCoreWires) e)
theorem rFullSysElecSlot_val {mPayload : ℕ} (hmPay : 80 ≤ mPayload) (e : Fin 218) (j : Fin 18) :
    (rFullSysElecSlot hmPay e j).val = 18 * e.val + j.val := by
  simp [rFullSysElecSlot, selPosInFullSys_val, rElecSlot, QRegister.slice, QRegExt.ofFin]
/-- General entry formula for `r.embedMatrix M` in terms of `SameOutside (Set.range r.wires)`. -/
theorem basisSplitEquiv_snd_eq_iff_sameOutside {k n : ℕ} (r : QRegister k n)
    (x y : Fin (2 ^ n)) : (r.basisSplitEquiv x).2 = (r.basisSplitEquiv y).2 ↔ SameOutside
    (Set.range r.wires) y x := by
  let x' := r.replaceIndex y (r.extractIndex x)
  have hx'1 : (r.basisSplitEquiv x').1 = (r.basisSplitEquiv x).1 := by
    rw [QRegister.basisSplitEquiv_apply_fst, QRegister.basisSplitEquiv_apply_fst,
        QRegister.extractIndex_replaceIndex]
  have hx'2 : (r.basisSplitEquiv x').2 = (r.basisSplitEquiv y).2 := by
    dsimp only [x']
    rw [r.basisSplitEquiv_replaceIndex]
  constructor
  · intro henv
    have hxx' : x' = x := r.basisSplitEquiv.injective (Prod.ext hx'1 (hx'2.trans henv.symm))
    intro w hw
    rw [← hxx', QRegister.basisBits_replaceIndex_of_not_mem r y _ w hw]
  · intro hSame
    have hxx' : x' = x := eq_of_basisBits_eq fun w ↦ by
      by_cases hw : w ∈ Set.range r.wires
      · obtain ⟨j, rfl⟩ := hw
        rw [QRegister.basisBits_replaceIndex_apply, QRegister.basisBits_extractIndex]
      · rw [QRegister.basisBits_replaceIndex_of_not_mem r y _ w hw, hSame w hw]
    rw [← hxx', hx'2]
open Classical in
theorem embedMatrix_apply_sameOutside {k n : ℕ} (r : QRegister k n) (M : Operator (2 ^ k))
    (x y : Fin (2 ^ n)) : (r.embedMatrix M) x y = if SameOutside (Set.range r.wires) y x then
    M (r.extractIndex x) (r.extractIndex y) else 0 := by
  rw [QRegister.embedMatrix_apply]
  by_cases hS : SameOutside (Set.range r.wires) y x
  · rw [ite_eq_left ((basisSplitEquiv_snd_eq_iff_sameOutside r x y).mpr hS), ite_eq_left hS,
      mul_one]
  · rw [ite_eq_right (fun h ↦ hS ((basisSplitEquiv_snd_eq_iff_sameOutside r x y).mp h)),
      ite_eq_right hS, mul_zero]
/-- Active 18-wire electron slot register `coinBarrelFastSlotReg hmPay x` selected by
  `coinBarrelIdxFast`
for `x : Fin (2 ^ (fullSysCoreWires mPayload))` (handling both `c2 = 0` and `c2 = 1`). -/
def coinBarrelFastSlotReg {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (x : Fin (2 ^ (fullSysCoreWires mPayload))) :
    QRegister 18 (fullSysCoreWires mPayload) :=
  rFullSysElecSlot hmPay (coinBarrelIdxFast hmPay (basisBits (fullSysCoreWires mPayload) x))
theorem coinBarrelIdxFast_replaceIndex_elecSlot {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (e : Fin 218) (x : Fin (2 ^ (fullSysCoreWires mPayload))) (v : Fin (2 ^ 18)) :
    coinBarrelIdxFast hmPay
      (basisBits (fullSysCoreWires mPayload) ((rFullSysElecSlot hmPay e).replaceIndex x v)) =
    coinBarrelIdxFast hmPay (basisBits (fullSysCoreWires mPayload) x) := by
  refine coinBarrelIdxFast_congr_high hmPay fun w hw ↦ ?_
  refine QRegister.basisBits_replaceIndex_of_not_mem (rFullSysElecSlot hmPay e) x v w ?_
  rintro ⟨j, rfl⟩
  rw [rFullSysElecSlot_val] at hw
  have := e.isLt; have := j.isLt; omega
theorem coinBarrelFastSlotReg_replaceIndex {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (x : Fin (2 ^ (fullSysCoreWires mPayload))) (v : Fin (2 ^ 18)) :
    coinBarrelFastSlotReg hmPay ((coinBarrelFastSlotReg hmPay x).replaceIndex x v) =
      coinBarrelFastSlotReg hmPay x := by
  dsimp only [coinBarrelFastSlotReg]
  rw [coinBarrelIdxFast_replaceIndex_elecSlot]
/-- **Core Momentum-Space `Slot18Lens (fullSysCoreWires mPayload)` (`coinBarrelFastSlot18Lens`)**:
Selects `rElec[coinBarrelIdxFast hmPay γ]` across all `80 ≤ mPayload` and both `c2 = 0` and `c2 =
1`! -/
noncomputable def coinBarrelFastSlot18Lens {mPayload : ℕ} (hmPay : 80 ≤ mPayload) :
    Slot18Lens (fullSysCoreWires mPayload) :=
  mkSlot18LensOfSlotReg (coinBarrelFastSlotReg hmPay) (coinBarrelFastSlotReg_replaceIndex hmPay)
/-- **Data-Level Momentum-Space `Slot18Lens kData` (`coinBarrelFastOnDataLens`)**:
Lifts `coinBarrelFastSlot18Lens hmPay` along any `selCoreInData : QRegister (fullSysCoreWires
mPayload) kData`. -/
noncomputable def coinBarrelFastOnDataLens {mPayload kData : ℕ} (hmPay : 80 ≤ mPayload)
    (selCoreInData : QRegister (fullSysCoreWires mPayload) kData) : Slot18Lens kData :=
    liftSlot18Lens selCoreInData (coinBarrelFastSlot18Lens hmPay)
theorem coinBarrelFastOnDataLens_tbl {mPayload kData : ℕ} (hmPay : 80 ≤ mPayload)
    (selCoreInData : QRegister (fullSysCoreWires mPayload) kData) (d : Fin (2 ^ kData)) :
    (coinBarrelFastOnDataLens hmPay selCoreInData).tbl d = (selCoreInData.compose
    (coinBarrelFastSlotReg hmPay (selCoreInData.extractIndex d))).extractIndex d := by
  dsimp [coinBarrelFastOnDataLens, liftSlot18Lens, coinBarrelFastSlot18Lens, mkSlot18LensOfSlotReg]
  rw [QRegister.extractIndex_compose]
theorem coinBarrelFastOnDataLens_updSlot {mPayload kData : ℕ} (hmPay : 80 ≤ mPayload)
    (selCoreInData : QRegister (fullSysCoreWires mPayload) kData) (d : Fin (2 ^ kData))
    (v : Fin (2 ^ 18)) : (coinBarrelFastOnDataLens hmPay selCoreInData).updSlot d v =
    (selCoreInData.compose (coinBarrelFastSlotReg hmPay (selCoreInData.extractIndex
    d))).replaceIndex d v := by
  dsimp [coinBarrelFastOnDataLens, liftSlot18Lens, coinBarrelFastSlot18Lens, mkSlot18LensOfSlotReg]
  apply eq_of_basisBits_eq; intro w
  by_cases hwC : w ∈ Set.range selCoreInData.wires
  · obtain ⟨u, rfl⟩ := hwC
    rw [QRegister.basisBits_replaceIndex_apply]
    let rS := coinBarrelFastSlotReg hmPay (selCoreInData.extractIndex d)
    by_cases huS : u ∈ Set.range rS.wires
    · obtain ⟨j, rfl⟩ := huS
      rw [QRegister.basisBits_replaceIndex_apply]
      exact (QRegister.basisBits_replaceIndex_apply (selCoreInData.compose rS) d v j).symm
    · rw [QRegister.basisBits_replaceIndex_of_not_mem rS _ v u huS,
          QRegister.basisBits_extractIndex,
          QRegister.basisBits_replaceIndex_of_not_mem (selCoreInData.compose rS) d v _
            (fun ⟨j, hj⟩ ↦ huS ⟨j, selCoreInData.wires.injective hj⟩)]
  · rw [QRegister.basisBits_replaceIndex_of_not_mem selCoreInData _ _ w hwC,
        QRegister.basisBits_replaceIndex_of_not_mem _ d v w (fun ⟨j, hj⟩ ↦ hwC ⟨_, hj⟩)]
end ImplBoothOpt_03
end BoothOpt_03_CoinBarrelIdxFastTrueSwap
end ScopeBoothOpt
set_option maxRecDepth 4096
namespace ButterflyBarrelSlot0Conj
open HermitianMat
open scoped ComplexOrder MatrixOrder
open SpecsAux SpecsAux.SpecMirror
open CoinDispatchedBarrel288 FullSysCatSegmentBridge
open FastCoinBarrelDecoder279
open MeasureBranchHadamardSem (ket bit_cases matrix_ext_ket)
def spectatorElecReg {mPayload kData : ℕ}
    (selCore : QRegister (fullSysCoreWires mPayload) kData) : QRegister 3906 kData :=
  selCore.slice 18 3906 (by
    dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits,
      SpecsAux.SpecMirror.numElectrons, SpecsAux.SpecMirror.electronBits,
        SpecsAux.SpecMirror.projectileBits]
    omega)
/-- A unitary `U` on `kData` qubits acts as the identity on the `217` spectator electron slots
`[18 .. 3924)` of `selCore` if `U.1` commutes with every operator embedded on `spectatorElecReg
selCore`. -/
def ActsAsIdOnSpectatorWires {mPayload kData : ℕ}
    (selCore : QRegister (fullSysCoreWires mPayload) kData) (U : Unitary (2 ^ kData)) : Prop
    := ∀ A : Matrix (Fin (2 ^ 3906)) (Fin (2 ^ 3906)) ℂ, U.1 *
    (spectatorElecReg selCore).embedMatrix A = (spectatorElecReg selCore).embedMatrix A * U.1
/-- A unitary `U` on `kData` qubits preserves all high core wires `3924 ≤ w.val < C` of `selCore`
if `U.1` commutes with every single-wire outcome projector on `selCore w` for `3924 ≤ w.val`. -/
def PreservesHigh3924On {mPayload kData : ℕ}
    (selCore : QRegister (fullSysCoreWires mPayload) kData) (U : Unitary (2 ^ kData)) : Prop
    := ∀ (w : Wire (fullSysCoreWires mPayload)), 3924 ≤ w.val → ∀ b : Fin 2, U.1 *
    (QRegister.singleton (selCore w)).basisOutcomeProjector b =
    (QRegister.singleton (selCore w)).basisOutcomeProjector b * U.1
theorem ActsAsIdOnSpectatorWires.one {mPayload kData : ℕ}
    (selCore : QRegister (fullSysCoreWires mPayload) kData) :
    ActsAsIdOnSpectatorWires selCore (1 : Unitary (2 ^ kData)) :=
  fun _ ↦ by simp
theorem ActsAsIdOnSpectatorWires.mul {mPayload kData : ℕ}
    {selCore : QRegister (fullSysCoreWires mPayload) kData}
    {U₁ U₂ : Unitary (2 ^ kData)}
    (h₁ : ActsAsIdOnSpectatorWires selCore U₁)
    (h₂ : ActsAsIdOnSpectatorWires selCore U₂) :
    ActsAsIdOnSpectatorWires selCore (U₁ * U₂) := fun A ↦ by
  simp only [Submonoid.coe_mul]
  calc (U₁.1 * U₂.1) * (spectatorElecReg selCore).embedMatrix A
      = U₁.1 * (U₂.1 * (spectatorElecReg selCore).embedMatrix A) := by rw [Matrix.mul_assoc]
    _ = (U₁.1 * (spectatorElecReg selCore).embedMatrix A) * U₂.1 := by rw [h₂ A, ← Matrix.mul_assoc]
    _ = (spectatorElecReg selCore).embedMatrix A * (U₁.1 * U₂.1) := by rw [h₁ A, Matrix.mul_assoc]
theorem ActsAsIdOnSpectatorWires.inv {mPayload kData : ℕ}
    {selCore : QRegister (fullSysCoreWires mPayload) kData}
    {U : Unitary (2 ^ kData)}
    (h : ActsAsIdOnSpectatorWires selCore U) :
    ActsAsIdOnSpectatorWires selCore U⁻¹ := fun A ↦ by
  have hUI : U.1 * (U⁻¹).1 = 1 := congrArg Subtype.val (mul_inv_cancel U)
  have hIU : (U⁻¹).1 * U.1 = 1 := congrArg Subtype.val (inv_mul_cancel U)
  calc (U⁻¹).1 * (spectatorElecReg selCore).embedMatrix A
      = (U⁻¹).1 * (spectatorElecReg selCore).embedMatrix A * (U.1 * (U⁻¹).1) := by
        rw [hUI, Matrix.mul_one]
    _ = (U⁻¹).1 * ((spectatorElecReg selCore).embedMatrix A * U.1) * (U⁻¹).1 := by
      simp only [Matrix.mul_assoc]
    _ = ((U⁻¹).1 * U.1) * (spectatorElecReg selCore).embedMatrix A * (U⁻¹).1 := by
        rw [← h A]; simp only [Matrix.mul_assoc]
    _ = (spectatorElecReg selCore).embedMatrix A * (U⁻¹).1 := by rw [hIU, Matrix.one_mul]
theorem ActsAsIdOnSpectatorWires.of_diagonal {mPayload kData : ℕ}
    (selCore : QRegister (fullSysCoreWires mPayload) kData)
    (U : Unitary (2 ^ kData)) (d : Fin (2 ^ kData) → ℂ)
    (hDiag : U.1 = Matrix.diagonal d)
    (hIndep : ∀ (β : BitAssignment kData) (δ : BitAssignment 3906),
      d ((basisBitsEquiv kData).symm (Internal.writeRegProg β (spectatorElecReg selCore) δ)) =
        d ((basisBitsEquiv kData).symm β)) :
    ActsAsIdOnSpectatorWires selCore U := fun A ↦ by
  rw [hDiag]
  apply matrix_ext_ket
  intro β
  have hdKet : ∀ γ : BitAssignment kData,
      (Matrix.diagonal d).mulVec (ket γ) = d ((basisBitsEquiv kData).symm γ) • ket γ := by
    intro γ; funext idx
    rw [ket, basisState, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.diagonal_apply]
    by_cases h : idx = (basisBitsEquiv kData).symm γ <;> simp [h]
  simp only [Internal.mul_mulVec_prog, hdKet, Matrix.mulVec_smul,
    Internal.embedMatrix_mulVec_ket_prog, Matrix.mulVec_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [hIndep β (basisBits 3906 l), smul_comm]
theorem PreservesHigh3924On.one {mPayload kData : ℕ}
    (selCore : QRegister (fullSysCoreWires mPayload) kData) :
    PreservesHigh3924On selCore (1 : Unitary (2 ^ kData)) :=
  fun _ _ _ ↦ by simp
theorem PreservesHigh3924On.mul {mPayload kData : ℕ}
    {selCore : QRegister (fullSysCoreWires mPayload) kData}
    {U₁ U₂ : Unitary (2 ^ kData)}
    (h₁ : PreservesHigh3924On selCore U₁)
    (h₂ : PreservesHigh3924On selCore U₂) :
    PreservesHigh3924On selCore (U₁ * U₂) := fun w hw b ↦ by
  simp only [Submonoid.coe_mul]
  calc (U₁.1 * U₂.1) * (QRegister.singleton (selCore w)).basisOutcomeProjector b
      = U₁.1 * (U₂.1 * (QRegister.singleton (selCore w)).basisOutcomeProjector b) := by
        rw [Matrix.mul_assoc]
    _ = (U₁.1 * (QRegister.singleton (selCore w)).basisOutcomeProjector b) * U₂.1 := by
        rw [h₂ w hw b, ← Matrix.mul_assoc]
    _ = (QRegister.singleton (selCore w)).basisOutcomeProjector b * (U₁.1 * U₂.1) := by
        rw [h₁ w hw b, Matrix.mul_assoc]
theorem PreservesHigh3924On.inv {mPayload kData : ℕ}
    {selCore : QRegister (fullSysCoreWires mPayload) kData}
    {U : Unitary (2 ^ kData)}
    (h : PreservesHigh3924On selCore U) :
    PreservesHigh3924On selCore U⁻¹ := fun w hw b ↦ by
  have hUI : U.1 * (U⁻¹).1 = 1 := congrArg Subtype.val (mul_inv_cancel U)
  have hIU : (U⁻¹).1 * U.1 = 1 := congrArg Subtype.val (inv_mul_cancel U)
  let P := (QRegister.singleton (selCore w)).basisOutcomeProjector b
  have hUP : U.1 * P = P * U.1 := h w hw b
  calc (U⁻¹).1 * P
      = (U⁻¹).1 * P * (U.1 * (U⁻¹).1) := by rw [hUI, Matrix.mul_one]
    _ = (U⁻¹).1 * (P * U.1) * (U⁻¹).1 := by simp only [Matrix.mul_assoc]
    _ = ((U⁻¹).1 * U.1) * P * (U⁻¹).1 := by rw [← hUP]; simp only [Matrix.mul_assoc]
    _ = P * (U⁻¹).1 := by rw [hIU, Matrix.one_mul]
theorem PreservesHigh3924On.of_diagonal {mPayload kData : ℕ}
    (selCore : QRegister (fullSysCoreWires mPayload) kData)
    (U : Unitary (2 ^ kData)) (d : Fin (2 ^ kData) → ℂ)
    (hDiag : U.1 = Matrix.diagonal d) :
    PreservesHigh3924On selCore U := fun w _ b ↦ by
  rw [hDiag, QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1; funext x; exact mul_comm _ _
theorem PreservesHigh3924On.entry_eq {mPayload kData : ℕ}
    {selCore : QRegister (fullSysCoreWires mPayload) kData} {U : Unitary (2 ^ kData)}
    (hHigh : PreservesHigh3924On selCore U) {y x : Fin (2 ^ kData)} (hzy : U.1 y x ≠ 0)
    (w : Wire (fullSysCoreWires mPayload)) (hw : 3924 ≤ w.val) : basisBits kData y
    (selCore w) = basisBits kData x (selCore w) := by
  let bx : Fin 2 := ⟨(basisBits kData x (selCore w)).val, ZMod.val_lt _⟩
  have hbx_ext : (QRegister.singleton (selCore w)).extractIndex x = bx := by
    have hb0 := (QRegister.singleton (selCore w)).basisBits_extractIndex x 0
    change basisBits 1 ((QRegister.singleton (selCore w)).extractIndex x) 0 =
      basisBits kData x (selCore w) at hb0
    rcases hex : (QRegister.singleton (selCore w)).extractIndex x with ⟨v, hv⟩
    rw [hex] at hb0
    rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl
    · have hz : basisBits 1 (⟨0, hv⟩ : Fin 2) 0 = 0 := (by decide : basisBits 1 (0 : Fin 2) 0 = 0)
      rw [hz] at hb0; exact Fin.ext (by dsimp [bx]; rw [← hb0]; rfl)
    · have ho : basisBits 1 (⟨1, hv⟩ : Fin 2) 0 = 1 := (by decide : basisBits 1 (1 : Fin 2) 0 = 1)
      rw [ho] at hb0; exact Fin.ext (by dsimp [bx]; rw [← hb0]; rfl)
  have hcomm := congrFun (congrFun (hHigh w hw bx) y) x
  rw [QRegister.basisOutcomeProjector_eq_diagonal, Matrix.mul_diagonal,
      Matrix.diagonal_mul] at hcomm
  simp only [hbx_ext, ↓reduceIte, mul_one] at hcomm
  by_cases hby : (QRegister.singleton (selCore w)).extractIndex y = bx
  · have hb0 := (QRegister.singleton (selCore w)).basisBits_extractIndex y 0
    change basisBits 1 ((QRegister.singleton (selCore w)).extractIndex y) 0 =
      basisBits kData y (selCore w) at hb0
    rw [hby] at hb0
    rcases bit_cases (basisBits kData x (selCore w)) with hx0 | hx1
    · have hbx0 : bx = 0 := Fin.ext (by dsimp [bx]; rw [hx0]; rfl)
      rw [hbx0] at hb0
      have hz : basisBits 1 (0 : Fin 2) 0 = 0 := by decide
      rw [hz] at hb0; rw [← hb0, hx0]
    · have hbx1 : bx = 1 := Fin.ext (by dsimp [bx]; rw [hx1]; rfl)
      rw [hbx1] at hb0
      have ho : basisBits 1 (1 : Fin 2) 0 = 1 := by decide
      rw [ho] at hb0; rw [← hb0, hx1]
  · simp only [hby, ↓reduceIte, zero_mul] at hcomm
    exact absurd hcomm hzy
end ButterflyBarrelSlot0Conj
namespace CoinBarrelPureCnotLoad
section ImplSub
set_option maxRecDepth 65536
set_option exponentiation.threshold 256
open SpecsAux SpecsAux.SpecMirror
open FullSysCatSegmentBridge (fullSysCoreWires)
open CoinDispatchedBarrel288
open InterWalkRSum42Hoist (qreg_ext qreg_block_apply rSegFull rCoreFull E_rawStream42)
open Barrel3PassSelectStitch (rCoreSeg)
open Leaf4Ext48TopStitch
open StageAPointPhase128OnStep (rCoreInCoreSum42)
open HeldStreamFoldedPass123Bridge (preservesRawStream42_uBarrelFast
  rCoreSeg_comm_E_rawStream42_of_preservesRaw)
/-- Extracting `rCoreInCoreSum42 mPayload` from `rCore.concat rSum42 hCS` recovers `rCore`. -/
@[simp] theorem concat_compose_rCoreInCoreSum42 {mPayload n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n) (rSum42 : QRegister 42 n)
    (hCS : rCore.DisjointWires rSum42) : (rCore.concat rSum42 hCS).compose
    (rCoreInCoreSum42 mPayload) = rCore := by
  apply qreg_ext
  intro q
  have hc : rCoreInCoreSum42 mPayload q = Fin.castAdd 42 q := by
    ext; simp [rCoreInCoreSum42]
  change (rCore.concat rSum42 hCS) (rCoreInCoreSum42 mPayload q) = rCore q
  rw [hc, QRegister.concat_apply_left]
/-- **Zero-Hypothesis `E_rawStream42` Commutation (`rSegFull` / `rCoreSeg` Form)**:
`(rSegFull.embedUnitary (rCoreSeg.embedUnitary (uBarrelFast (le_refl 80)))).1` commutes with
`E_rawStream42`. -/
theorem uBarrelFast_comm_E_rawStream42 :
    (rSegFull.embedUnitary (rCoreSeg.embedUnitary (uBarrelFast (le_refl 80)))).1 * E_rawStream42 =
      E_rawStream42 * (rSegFull.embedUnitary (rCoreSeg.embedUnitary (uBarrelFast (le_refl 80)))).1
          :=
  rCoreSeg_comm_E_rawStream42_of_preservesRaw preservesRawStream42_uBarrelFast
/-- Disjointness of `rCoreFull` (`[0 .. 4034)`) and `rPGIdle k_idle hk` (`[4035 .. 4035 +
  k_idle)`). -/
theorem rCoreFull_disj_rPGIdle (k_idle : ℕ) (hk : k_idle ≤ 48) :
    rCoreFull.DisjointWires (rPGIdle k_idle hk) :=
  disj_of_val_ne fun i q ↦ by
    rw [rCoreFull_val_eq, rPGIdle_val_eq]
    have hi := i.isLt; have hq := q.isLt
    dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
      SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits] at hi
    omega
end ImplSub
end CoinBarrelPureCnotLoad
namespace BarrelPass2AndHeld3PassSelectStitch
section ImplK2
set_option maxRecDepth 65536
open SpecsAux SpecsAux.SpecMirror
open FullSysCatSegmentBridge (fullSysCoreWires fullSysBEWires)
open InterWalkRSum42Hoist (qreg_ext kFull80 rAct0 rSegOrig rSegFull E_rawStream42)
open Barrel3PassSelectStitch (rCoreSeg)
open Leaf4Ext48TopStitch (CommutesWithReg basisOutcomeProjector_comm_any pCtrl3Zero
  pExt6IdleZero_eq_pCtrl3_mul_pSlackIdle pPGIdleZero pSlack3Zero rCtrl3InCore rPGIdle rPGIdleOrig
  rSlack3Full)
open SelectHoistLemmas (rCtrl3InSeg)
open SelectExtStitch (rSegFull_compose_rCoreSeg_eq rCoreFull_compose_rCtrl3InCore)
open HeldStreamFoldedPass123Bridge (E_rawCtrl3Ext E_rawSegExt)
open SelectHoistLemmas (rSegFull_compose_rCtrl3InSeg rSegFull_eq_rAct0_compose_rSegOrig
  rSegFull_comm_pSlack3Zero)
/-- Universal raw-stream-to-extended-subspace intertwiner: any full `kFull80` operator `U`
satisfying `U * E_rawStream42 = E_rawStream42 * (rSegFull.embedUnitary uSeg).1` (for instance a
stream-assisted Stage-A or Stage-B circuit acting freely on `rSum0` and swapping `Ctrl3` onto
idle catalyst wires) automatically intertwines **both** `E_rawCtrl3Ext k_idle hk` (`Ctrl`) and
`E_rawSegExt k_idle hk` (`Cat`) with `(rSegFull.embedUnitary uSeg).1`! -/
theorem rawStream_intertwine_to_rawCtrl3Ext_and_rawSegExt {k_idle : ℕ} (hk : k_idle ≤ 48)
    (U : Operator (2 ^ kFull80)) (uSeg : Unitary (2 ^ (fullSysBEWires 80 + 48))) (hRaw : U *
    E_rawStream42 = E_rawStream42 * (rSegFull.embedUnitary uSeg).1)
    (hCtrl3 : CommutesWithReg rCtrl3InSeg uSeg.1) (hIdle : CommutesWithReg (rPGIdleOrig k_idle
    hk) (rSegOrig.embedUnitary uSeg).1) : U * E_rawCtrl3Ext k_idle hk = E_rawCtrl3Ext k_idle
    hk * (rSegFull.embedUnitary uSeg).1 ∧ U * E_rawSegExt k_idle hk = E_rawSegExt k_idle hk *
    (rSegFull.embedUnitary uSeg).1 := by
  let M := rSegFull.embedUnitary uSeg
  have hMCtrl : M.1 * pCtrl3Zero = pCtrl3Zero * M.1 := by
    have hc := (CommutesWithReg.embedMatrix rSegFull hCtrl3).comm_basisOutcomeProjector 0
    rwa [rSegFull_compose_rCtrl3InSeg] at hc
  have hMIdle : M.1 * pPGIdleZero k_idle hk = pPGIdleZero k_idle hk * M.1 := by
    have hEmb : rAct0.embedMatrix ((rPGIdleOrig k_idle hk).basisOutcomeProjector 0) =
        pPGIdleZero k_idle hk :=
      (QRegister.embedMatrix_compose rAct0 (rPGIdleOrig k_idle hk) (compProj 0)).symm
    have hMEq : rAct0.embedMatrix (rSegOrig.embedUnitary uSeg).1 = M.1 := by
      dsimp only [M]
      rw [rSegFull_eq_rAct0_compose_rSegOrig, QRegister.embedUnitary_compose]
      exact (rAct0.embedUnitary_val (rSegOrig.embedUnitary uSeg)).symm
    have hi := congrArg rAct0.embedMatrix (hIdle.comm_basisOutcomeProjector 0)
    rw [rAct0.embedMatrix_mul, rAct0.embedMatrix_mul, hMEq, hEmb] at hi
    exact hi
  have hCtrlExt : U * E_rawCtrl3Ext k_idle hk = E_rawCtrl3Ext k_idle hk * M.1 := by
    unfold E_rawCtrl3Ext
    rw [← Matrix.mul_assoc, hRaw, Matrix.mul_assoc, ← Matrix.mul_assoc M.1 pCtrl3Zero,
      hMCtrl, Matrix.mul_assoc pCtrl3Zero, hMIdle, ← Matrix.mul_assoc pCtrl3Zero, ←
          Matrix.mul_assoc]
  refine ⟨hCtrlExt, ?_⟩
  have hSlk : M.1 * pSlack3Zero = pSlack3Zero * M.1 := rSegFull_comm_pSlack3Zero uSeg
  have hEq : E_rawSegExt k_idle hk = E_rawCtrl3Ext k_idle hk * pSlack3Zero := by
    unfold E_rawSegExt E_rawCtrl3Ext
    rw [pExt6IdleZero_eq_pCtrl3_mul_pSlackIdle, Leaf4Ext48TopStitch.pSlackIdleZero_eq_mul]
    unfold pSlack3Zero pPGIdleZero
    rw [basisOutcomeProjector_comm_any rSlack3Full 0 (rPGIdle k_idle hk) 0,
      ← Matrix.mul_assoc pCtrl3Zero, ← Matrix.mul_assoc E_rawStream42]
  rw [hEq, ← Matrix.mul_assoc, hCtrlExt, Matrix.mul_assoc, hSlk, ← Matrix.mul_assoc]
/-- Core-embedded specialization of `rawStream_intertwine_to_rawCtrl3Ext_and_rawSegExt`:
requires **only** `CommutesWithReg rCtrl3InCore uCore.1` (`rCoreOrig` is disjoint from
`rPGIdleOrig`). -/
theorem rawStream_core_intertwine_to_rawCtrl3Ext_and_rawSegExt {k_idle : ℕ} (hk : k_idle ≤ 48)
    (U : Operator (2 ^ kFull80)) (uCore : Unitary (2 ^ (fullSysCoreWires 80))) (hRaw : U *
    E_rawStream42 = E_rawStream42 * (rSegFull.embedUnitary (rCoreSeg.embedUnitary uCore)).1)
    (hCtrl3 : CommutesWithReg rCtrl3InCore uCore.1) : U * E_rawCtrl3Ext k_idle hk =
    E_rawCtrl3Ext k_idle hk * (rSegFull.embedUnitary (rCoreSeg.embedUnitary uCore)).1 ∧ U *
    E_rawSegExt k_idle hk = E_rawSegExt k_idle hk *
    (rSegFull.embedUnitary (rCoreSeg.embedUnitary uCore)).1 := by
  have hSegCtrl3 : CommutesWithReg rCtrl3InSeg (rCoreSeg.embedUnitary uCore).1 := by
    have hc := CommutesWithReg.embedMatrix rCoreSeg hCtrl3
    have hEq : rCoreSeg.compose rCtrl3InCore = rCtrl3InSeg := by
      apply qreg_ext; intro i
      exact rSegFull.wires.injective (by
        change (rSegFull.compose (rCoreSeg.compose rCtrl3InCore)) i =
          (rSegFull.compose rCtrl3InSeg) i
        rw [← QRegister.compose_assoc, rSegFull_compose_rCoreSeg_eq,
          rCoreFull_compose_rCtrl3InCore])
    rwa [hEq] at hc
  have hSegIdle : CommutesWithReg (rPGIdleOrig k_idle hk)
      (rSegOrig.embedUnitary (rCoreSeg.embedUnitary uCore)).1 := by
    have hDisjOrig : (rSegOrig.compose rCoreSeg).DisjointWires (rPGIdleOrig k_idle hk) := by
      rw [QRegister.disjoint_iff]; intro i q h
      have hAct := congrArg rAct0 h
      change (rAct0.compose (rSegOrig.compose rCoreSeg)) i = (rPGIdle k_idle hk) q at hAct
      rw [← QRegister.compose_assoc, ← rSegFull_eq_rAct0_compose_rSegOrig,
        rSegFull_compose_rCoreSeg_eq] at hAct
      exact (CoinBarrelPureCnotLoad.rCoreFull_disj_rPGIdle k_idle hk).ne i q
          hAct
    rw [← QRegister.embedUnitary_compose, QRegister.embedUnitary_val]
    exact CommutesWithReg.of_disjoint hDisjOrig uCore.1
  exact rawStream_intertwine_to_rawCtrl3Ext_and_rawSegExt hk U (rCoreSeg.embedUnitary uCore)
    hRaw hSegCtrl3 hSegIdle
end ImplK2
end BarrelPass2AndHeld3PassSelectStitch
set_option maxRecDepth 65536
set_option exponentiation.threshold 256
namespace ZeroHyp5StepA3StepBMidEqAndUncondExt48
section ImplCleanSub
open HermitianMat
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open DyadicQft64WalkCircuit (rAxis654 rElec18In654)
open InterWalkRSum42Hoist (qreg_ext)
open HeldRSum42TwistQftPass2Stitch (rAxisPrefix axisProdPrefix)
open StageAPosHeadConjugatedCircuit (uCoreHadamard6 uCoreHadamard18)
open ForestQft117BundleNoTopBridge (activeOneElecForestQftBundle128
  activeOneElecForestQftBundle_uQft654)
theorem rElec18In654_embedUnitary_uCoreHadamard18 (i : Fin 218) :
    (rElec18In654 i).embedUnitary uCoreHadamard18 =
      (rAxis654 ⟨3 * i.val, by omega⟩).embedUnitary uCoreHadamard6 *
        (rAxis654 ⟨3 * i.val + 1, by omega⟩).embedUnitary uCoreHadamard6 *
        (rAxis654 ⟨3 * i.val + 2, by omega⟩).embedUnitary uCoreHadamard6 := by
  have hr0 : (rElec18In654 i).compose (QRegister.block 0 6 (by decide)) =
      rAxis654 ⟨3 * i.val, by omega⟩ := by
    apply qreg_ext; intro r; apply Fin.ext
    change 18 * i.val + (0 + r.val) = 6 * (3 * i.val) + r.val; omega
  have hr1 : (rElec18In654 i).compose (QRegister.block 6 6 (by decide)) =
      rAxis654 ⟨3 * i.val + 1, by omega⟩ := by
    apply qreg_ext; intro r; apply Fin.ext
    change 18 * i.val + (6 + r.val) = 6 * (3 * i.val + 1) + r.val; omega
  have hr2 : (rElec18In654 i).compose (QRegister.block 12 6 (by decide)) =
      rAxis654 ⟨3 * i.val + 2, by omega⟩ := by
    apply qreg_ext; intro r; apply Fin.ext
    change 18 * i.val + (12 + r.val) = 6 * (3 * i.val + 2) + r.val; omega
  rw [uCoreHadamard18, (rElec18In654 i).embedUnitary_mul, (rElec18In654 i).embedUnitary_mul,
    ← QRegister.embedUnitary_compose, ← QRegister.embedUnitary_compose,
    ← QRegister.embedUnitary_compose, hr0, hr1, hr2]
/-- Exact 18-wire factorization of `activeOneElecForestQftBundle128.uQft654`. -/
theorem activeOneElecForestQftBundle128_uQft654_eq_rElec18In654_zero :
    activeOneElecForestQftBundle128.uQft654 =
      (rElec18In654 0).embedUnitary uCoreHadamard18 := by
  rw [activeOneElecForestQftBundle_uQft654 128 le_rfl, rElec18In654_embedUnitary_uCoreHadamard18 0]
  dsimp only [axisProdPrefix, rAxisPrefix]
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  rfl
end ImplCleanSub
end ZeroHyp5StepA3StepBMidEqAndUncondExt48
namespace ZeroHypCatState48StageABMidCoreReductionAn
section ImplCleanAux
open HermitianMat
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open FullSysCatSegmentBridge (fullSysBEWires)
open CatalystPrep (U_cat_B_normalized)
open Barrel3PassSelectStitch (rCat80)
/-- The 48-qubit phase-gradient catalyst state operator on `fullSysBEWires 80 + 48`. -/
noncomputable def catState48 : Operator (2 ^ (fullSysBEWires 80 + 48)) :=
  (rCat80.embedUnitary (U_cat_B_normalized 48)).1 * rCat80.basisOutcomeProjector 0
end ImplCleanAux
end ZeroHypCatState48StageABMidCoreReductionAn
namespace ZeroHypStageABToUFoldedPass123SegAndCompac
section ImplClean
open HermitianMat
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open DyadicQft64WalkCircuit (prod_ofFn_group3 rAxis654 rElec18In654 stageH654 stageD654 axisProd654
  axisProd654_mul stageH654_eq_axisProd stageD654_eq_axisProd)
open CoreQftHadamardPrunedCore (coreQftHadamardPrunedBundle128)
open FullSysCatSegmentBridge (fullSysCoreWires fullSysQftCoreUnitary coreElecCosetB1Block)
open PosSlots24SemanticBridge (pos24_coreWires80_eq castUnitaryPow2)
open PosSlots24Barrel3Pass (permUnitary_apply)
open PosHeadMod4_15476 (flipThClean flipThClean_apply_ne permThClean diagZ8UnitaryN
  monomialZ8UnitaryN uHeadPhaseMod4)
open PosPostPrep80MergedVep (uSwapCore3967)
open StageAPosHeadConjugatedCircuit (uCoreHadamard6 uCoreHadamard18)
theorem embedUnitary_list_ofFn_prod {m k N : ℕ} (rOuter : QRegister k N) :
    ∀ {n : ℕ} (rInner : Fin n → QRegister m k) (V : Fin n → Unitary (2 ^ m)),
      rOuter.embedUnitary ((List.ofFn fun i ↦ (rInner i).embedUnitary (V i)).prod) =
        (List.ofFn fun i ↦ (rOuter.compose (rInner i)).embedUnitary (V i)).prod
  | 0, _, _ => by simp [QRegister.embedUnitary_one]
  | n + 1, rInner, V => by
      rw [List.ofFn_succ, List.prod_cons, QRegister.embedUnitary_mul,
          embedUnitary_list_ofFn_prod rOuter (fun i ↦ rInner i.succ) (fun i ↦ V i.succ),
          ← QRegister.embedUnitary_compose, List.ofFn_succ, List.prod_cons]
theorem axisProd654_const_eq_elecGroup218 (U_1D : Unitary 64) :
    axisProd654 (fun _ ↦ U_1D) =
      (List.ofFn fun i : Fin 218 ↦
        (rAxis654 ⟨3 * i.val, by omega⟩).embedUnitary U_1D *
          (rAxis654 ⟨3 * i.val + 1, by omega⟩).embedUnitary U_1D *
          (rAxis654 ⟨3 * i.val + 2, by omega⟩).embedUnitary U_1D).prod :=
  prod_ofFn_group3 218 (fun a ↦ (rAxis654 a).embedUnitary U_1D)
theorem coreQftHadamardBundle220_uQft654_eq_axisProd :
    coreQftHadamardPrunedBundle128.uQft654 = axisProd654 (fun _ ↦ uCoreHadamard6) := by
  have hdef : coreQftHadamardPrunedBundle128.uQft654 = stageH654 0 * (stageD654 1 * stageH654 1) *
      (stageD654 2 * stageH654 2) * (stageD654 3 * stageH654 3) * (stageD654 4 * stageH654 4)
      * (stageD654 5 * stageH654 5) := rfl
  rw[hdef, stageH654_eq_axisProd, stageD654_eq_axisProd, stageH654_eq_axisProd,
      stageD654_eq_axisProd, stageH654_eq_axisProd, stageD654_eq_axisProd,
      stageH654_eq_axisProd, stageD654_eq_axisProd, stageH654_eq_axisProd,
      stageD654_eq_axisProd, stageH654_eq_axisProd, axisProd654_mul, axisProd654_mul,
      axisProd654_mul, axisProd654_mul, axisProd654_mul, axisProd654_mul, axisProd654_mul,
      axisProd654_mul, axisProd654_mul, axisProd654_mul]
  rfl
open ZeroHyp5StepA3StepBMidEqAndUncondExt48
  (rElec18In654_embedUnitary_uCoreHadamard18) in
theorem coreQftHadamardBundle220_uQft654_eq_elecProd218 : coreQftHadamardPrunedBundle128.uQft654 =
    (List.ofFn fun i : Fin 218 ↦ (rElec18In654 i).embedUnitary uCoreHadamard18).prod := by
  rw [coreQftHadamardBundle220_uQft654_eq_axisProd, axisProd654_const_eq_elecGroup218]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  exact (rElec18In654_embedUnitary_uCoreHadamard18 i).symm
/-- 18-qubit register of electron `i : Fin 218` inside `fullSysCoreWires mPayload`. -/
def rElec18InCore {mPayload : ℕ} (hm6 : 6 ≤ mPayload) (i : Fin 218) : QRegister 18
    (fullSysCoreWires mPayload) := (coreElecCosetB1Block hm6).compose (rElec18In654 i)
theorem rElec18InCore_apply_val {mPayload : ℕ} (hm6 : 6 ≤ mPayload) (i : Fin 218) (j : Fin 18) :
    (rElec18InCore hm6 i j).val = 18 * i.val + j.val := by
  have hj : 18 * i.val + j.val < 3924 := by have := i.isLt; have := j.isLt; omega
  have hcast : rElec18In654 i j = Fin.castAdd 3 ⟨18 * i.val + j.val, hj⟩ := Fin.ext rfl
  change ((coreElecCosetB1Block hm6) (rElec18In654 i j)).val = _
  rw [hcast, QRegister.concat_apply_left]
  change 0 + (18 * i.val + j.val) = 18 * i.val + j.val
  omega
theorem rElec18InCore_disjoint {mPayload : ℕ} (hm6 : 6 ≤ mPayload) {i₁ i₂ : Fin 218}
    (hne : i₁ ≠ i₂) : (rElec18InCore hm6 i₁).DisjointWires (rElec18InCore hm6 i₂) := by
  have hv : i₁.val ≠ i₂.val := fun h ↦ hne (Fin.ext h)
  rw [QRegister.disjoint_iff]
  intro j₁ j₂ h
  have hval := congrArg Fin.val h
  rw [rElec18InCore_apply_val, rElec18InCore_apply_val] at hval
  have := j₁.isLt; have := j₂.isLt
  omega
/-- `fullSysQftCoreUnitary hm6 coreQftHadamardPrunedBundle128` equals the 218-electron product of
`(rElec18InCore hm6 i).embedUnitary uCoreHadamard18`. -/
theorem fullSysQftCoreUnitary_coreQftHadamardPrunedBundle128
    {mPayload : ℕ} (hm6 : 6 ≤ mPayload) :
    fullSysQftCoreUnitary hm6 coreQftHadamardPrunedBundle128 =
      (List.ofFn fun i : Fin 218 ↦ (rElec18InCore hm6 i).embedUnitary uCoreHadamard18).prod := by
  dsimp only [fullSysQftCoreUnitary, rElec18InCore]
  rw [coreQftHadamardBundle220_uQft654_eq_elecProd218]
  exact embedUnitary_list_ofFn_prod (coreElecCosetB1Block hm6)
    rElec18In654 (fun _ ↦ uCoreHadamard18)
/-- Full 218-electron product of `U : Unitary (2 ^ 18)` embedded on `rElec18InCore hm6 i`. -/
noncomputable def elecProd218 {mPayload : ℕ} (hm6 : 6 ≤ mPayload) (U : Unitary (2 ^ 18)) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  (List.ofFn fun i : Fin 218 ↦ (rElec18InCore hm6 i).embedUnitary U).prod
/-- Effective `fullSysCoreWires 80` Mod-4 Head unitary (`uSwapCore3967`-conjugated
  `uHeadPhaseMod4`). -/
noncomputable def uHeadPhase80Mod4Eff : Unitary (2 ^ (fullSysCoreWires 80)) :=
  (uSwapCore3967 * castUnitaryPow2 pos24_coreWires80_eq.symm uHeadPhaseMod4) * uSwapCore3967
/-- Electron `0` (`[0 .. 18)`) subregister inside `fullSysCoreWires mPayload + 42`. -/
def rElec0InCoreSum42 (mPayload : ℕ) : QRegister 18 (fullSysCoreWires mPayload + 42) :=
  QRegister.block 0 18 (by
    dsimp [fullSysCoreWires, SpecsAux.SpecMirror.systemQubits, SpecsAux.SpecMirror.numElectrons,
      SpecsAux.SpecMirror.electronBits, SpecsAux.SpecMirror.projectileBits]
    omega)
/-- Universal commutation of `monomialZ8UnitaryN wTh d p` with any diagonal matrix `Matrix.diagonal
  f`
whose diagonal entries `f` are invariant under flipping wire `wTh`. -/
theorem monomialZ8UnitaryN_comm_diagonal_of_invariant {n : ℕ} (wTh : Wire n)
    (d : BitAssignment n → Bool) (p : BitAssignment n → ZMod 8) (f : Fin (2 ^ n) → ℂ) (hInv :
    ∀ x y : Fin (2 ^ n), (∀ w : Wire n, w ≠ wTh → basisBits n x w = basisBits n y w) → f x = f
    y) : (monomialZ8UnitaryN wTh d p).1 * Matrix.diagonal f = Matrix.diagonal f *
    (monomialZ8UnitaryN wTh d p).1 := by
  have hDiagComm : (diagZ8UnitaryN p).1 * Matrix.diagonal f =
      Matrix.diagonal f * (diagZ8UnitaryN p).1 := by
    change Matrix.diagonal _ * Matrix.diagonal f = Matrix.diagonal f * Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun _ ↦ mul_comm _ _)
  have hPermComm : (Operator.permutationUnitary (permThClean wTh d)).1 * Matrix.diagonal f =
      Matrix.diagonal f * (Operator.permutationUnitary (permThClean wTh d)).1 := by
    ext x y
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hP : (Operator.permutationUnitary (permThClean wTh d)).1 x y = 0
    · simp [hP]
    · have hxy : x = permThClean wTh d y := by
        rw [permUnitary_apply] at hP
        by_contra hne; exact hP (ite_eq_right hne)
      have hf : f y = f x :=
        (hInv x y fun w hw ↦ by
          rw [hxy]
          dsimp only [permThClean, Equiv.coe_fn_mk]
          have hbb := congrFun ((basisBitsEquiv n).apply_symm_apply
            (flipThClean wTh d (basisBits n y))) w
          change basisBits n ((basisBitsEquiv n).symm
            (flipThClean wTh d (basisBits n y))) w = _ at hbb
          rw [hbb]
          exact flipThClean_apply_ne wTh d (basisBits n y) hw).symm
      rw [hf, mul_comm]
  dsimp only [monomialZ8UnitaryN, Submonoid.coe_mul]
  calc (Operator.permutationUnitary (permThClean wTh d)).1 * (diagZ8UnitaryN p).1 *
        Matrix.diagonal f
      = (Operator.permutationUnitary (permThClean wTh d)).1 *
          ((diagZ8UnitaryN p).1 * Matrix.diagonal f) := by
          simp only [Matrix.mul_assoc]
    _ = (Operator.permutationUnitary (permThClean wTh d)).1 *
          (Matrix.diagonal f * (diagZ8UnitaryN p).1) := by
          rw [hDiagComm]
    _ = ((Operator.permutationUnitary (permThClean wTh d)).1 * Matrix.diagonal f) *
          (diagZ8UnitaryN p).1 := by
          simp only [Matrix.mul_assoc]
    _ = Matrix.diagonal f *
          ((Operator.permutationUnitary (permThClean wTh d)).1 * (diagZ8UnitaryN p).1) := by
          rw [hPermComm]; simp only [Matrix.mul_assoc]
end ImplClean
end ZeroHypStageABToUFoldedPass123SegAndCompac
namespace ZeroHypLHSStageAB7Step3StepCatState48Proje
section ImplCleanAlt
open HermitianMat
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux SpecsAux.SpecMirror
open CoreQftHadamard140And160 (CanonStageSpec128 toFullSysQft654BundleOfLe128)
open FullSysCatSegmentBridge (fullSysCoreWires coreElecCosetB1Block IntertwinesLocalCat)
open CatalystPrep (U_cat_B_normalized)
open SingleCatSpine (U_cat_B_normalized_col_zero_singleCat)
open PosSlots24SemanticBridge (pos24_6_le_80)
open InterWalkRSum42Hoist (qreg_ext qreg_block_apply)
open StageAPointPhase128OnStep (rCoreInCoreSum42)
open FullConcrete7StepAndTrueSwapSelect (selCatInCoreSum42PG7)
/-- Universal `IntertwinesLocalCat` for any `S : CanonStageSpec128`. -/
theorem intertwinesLocalCat_canonStageSpec128_zeroHyp (S : CanonStageSpec128) :
    IntertwinesLocalCat (U_cat_B_normalized 7) S.uCat S.uEff ∧
    IntertwinesLocalCat (U_cat_B_normalized 7) S.uCat⁻¹ S.uEff⁻¹ := by
  have hFwd : IntertwinesLocalCat (U_cat_B_normalized 7) S.uCat S.uEff :=
    (toFullSysQft654BundleOfLe128 S 128 le_rfl).hIntertwinesQft
      (U_cat_B_normalized 7) (U_cat_B_normalized_col_zero_singleCat 7)
  exact ⟨hFwd, IntertwinesLocalCat.inv hFwd⟩
/-- `(3924 + 3)`-wire core-electron+coset selector inside `fullSysCoreWires 80 + 42`. -/
def rIdInCoreSum42 : QRegister (3924 + 3) (fullSysCoreWires 80 + 42) :=
  (rCoreInCoreSum42 80).compose (coreElecCosetB1Block pos24_6_le_80)
theorem concat_compose_selCatInCoreSum42PG7 {n : ℕ}
    (rCS : QRegister (fullSysCoreWires 80 + 42) n) (rPG7 : QRegister 7 n)
    (hCS_PG : rCS.DisjointWires rPG7) : (rCS.concat rPG7 hCS_PG).compose selCatInCoreSum42PG7
    = (rCS.compose rIdInCoreSum42).concat rPG7 (hCS_PG.compose_left rIdInCoreSum42) := by
  apply qreg_ext; intro idx
  refine Fin.addCases (fun i ↦ ?_) (fun m ↦ ?_) idx
  · rw [QRegister.compose_apply, QRegister.concat_apply_left, QRegister.compose_apply]
    have hLeft : selCatInCoreSum42PG7 (Fin.castAdd 7 i) = Fin.castAdd 7 (rIdInCoreSum42 i) := by
      apply Fin.ext
      change (selCatInCoreSum42PG7 (Fin.castAdd 7 i)).val = (rIdInCoreSum42 i).val
      unfold selCatInCoreSum42PG7 rIdInCoreSum42
      rw [QRegister.concat_apply_left]
      rfl
    rw [hLeft, QRegister.concat_apply_left]
  · rw [QRegister.compose_apply, QRegister.concat_apply_right]
    have hRight : selCatInCoreSum42PG7 (Fin.natAdd (3924 + 3) m) =
        Fin.natAdd (fullSysCoreWires 80 + 42) m := by
      apply Fin.ext
      change (selCatInCoreSum42PG7 (Fin.natAdd (3924 + 3) m)).val =
        (fullSysCoreWires 80 + 42) + m.val
      unfold selCatInCoreSum42PG7
      rw [QRegister.concat_apply_right]
      simp
    rw [hRight, QRegister.concat_apply_right]
end ImplCleanAlt
end ZeroHypLHSStageAB7Step3StepCatState48Proje
set_option exponentiation.threshold 8192
namespace SingleBarrel8StepClean
open SpecsAux SpecsAux.SpecMirror
open FullSysCatSegmentBridge (fullSysCoreWires fullSysBEWires fullSysQftCoreUnitary)
open CatalystPrep (U_cat_B_normalized)
open CoreQftHadamardPrunedCore (coreQftHadamardPrunedBundle128)
open InterWalkRSum42Hoist (kActOrig qreg_ext qreg_block_apply)
open Barrel3PassSelectStitch (hm6_80 rCoreSeg rCat80 hCoreSeg_disj_Cat80 uTrailCliffordXor80)
open Leaf4Ext48TopStitch (CommutesWithReg rPGIdleOrig)
open ZeroHypCatState48StageABMidCoreReductionAn (catState48)
section Part1A_GuardInitAndSwap4046
theorem commutesWithReg_sub {k₁ k₂ N : ℕ} {r₂ : QRegister k₂ N} (sub : QRegister k₁ k₂)
    {A : Operator (2 ^ N)} (h : CommutesWithReg r₂ A) :
    CommutesWithReg (r₂.compose sub) A := fun M ↦ by
  rw [QRegister.embedMatrix_compose]; exact h (sub.embedMatrix M)
end Part1A_GuardInitAndSwap4046
section Part1B_Ghost334AndSingleBarrel6Step
/-- 218-electron core QFT unitary `fullSysQftCoreUnitary hm6_80 coreQftHadamardPrunedBundle128`. -/
noncomputable abbrev qftCoreUnitary80 : Unitary (2 ^ (fullSysCoreWires 80)) :=
  fullSysQftCoreUnitary hm6_80 coreQftHadamardPrunedBundle128
/-- Combined QFT + trailing XOR32 Clifford core unitary `qftCoreUnitary80 * uTrailCliffordXor80`. -/
noncomputable abbrev qftCliffordCore80 : Unitary (2 ^ (fullSysCoreWires 80)) :=
  qftCoreUnitary80 * uTrailCliffordXor80
theorem rCoreSeg_comm_catState48 (V : Unitary (2 ^ (fullSysCoreWires 80))) :
    (rCoreSeg.embedUnitary V).1 * catState48 = catState48 * (rCoreSeg.embedUnitary V).1 := by
  have h1 : (rCoreSeg.embedUnitary V).1 * (rCat80.embedUnitary (U_cat_B_normalized 48)).1 =
      (rCat80.embedUnitary (U_cat_B_normalized 48)).1 * (rCoreSeg.embedUnitary V).1 := by
    rw [QRegister.embedUnitary_val, QRegister.embedUnitary_val]
    exact QRegister.embedMatrix_comm_of_disjoint rCoreSeg rCat80 hCoreSeg_disj_Cat80
      V.1 (U_cat_B_normalized 48).1
  have h2 : (rCoreSeg.embedUnitary V).1 * rCat80.basisOutcomeProjector 0 =
      rCat80.basisOutcomeProjector 0 * (rCoreSeg.embedUnitary V).1 := by
    rw [QRegister.embedUnitary_val]
    exact (QRegExt.embedMatrix_comm_basisOutcomeProjector_of_disjoint rCoreSeg) rCat80
      hCoreSeg_disj_Cat80 V.1 0
  unfold catState48
  rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc, h2, ← Matrix.mul_assoc]
theorem mul_catState48_comp {U2 U1 : Unitary (2 ^ (fullSysBEWires 80 + 48))}
    {V2 V1 : Unitary (2 ^ (fullSysCoreWires 80))}
    (h2 : U2.1 * catState48 = (rCoreSeg.embedUnitary V2).1 * catState48)
    (h1 : U1.1 * catState48 = (rCoreSeg.embedUnitary V1).1 * catState48) :
    (U2 * U1).1 * catState48 = (rCoreSeg.embedUnitary (V2 * V1)).1 * catState48 := by
  calc (U2 * U1).1 * catState48
    _ = U2.1 * (U1.1 * catState48) := by rw [Submonoid.coe_mul, Matrix.mul_assoc]
    _ = U2.1 * ((rCoreSeg.embedUnitary V1).1 * catState48) := by rw [h1]
    _ = (U2.1 * catState48) * (rCoreSeg.embedUnitary V1).1 := by
          rw [rCoreSeg_comm_catState48 V1, ← Matrix.mul_assoc]
    _ = ((rCoreSeg.embedUnitary V2).1 * catState48) * (rCoreSeg.embedUnitary V1).1 := by rw [h2]
    _ = (rCoreSeg.embedUnitary (V2 * V1)).1 * catState48 := by
          rw [Matrix.mul_assoc, ← rCoreSeg_comm_catState48 V1, ← Matrix.mul_assoc,
            ← Submonoid.coe_mul, ← QRegister.embedUnitary_mul]
theorem commutesWithReg_rPGIdleOrig11_of_12 {M : Operator (2 ^ kActOrig)}
    (h12 : CommutesWithReg (rPGIdleOrig 12 (by decide)) M) :
    CommutesWithReg (rPGIdleOrig 11 (by decide)) M := by
  have hSub : rPGIdleOrig 11 (by decide) =
      (rPGIdleOrig 12 (by decide)).compose (QRegister.block 0 11 (by decide)) := by
    apply qreg_ext; intro i
    apply Fin.ext
    rw [QRegister.compose_apply,
        Leaf4Ext48TopStitch.rPGIdleOrig_val_eq,
        Leaf4Ext48TopStitch.rPGIdleOrig_val_eq,
        qreg_block_apply]
    dsimp only
    omega
  rw [hSub]
  exact commutesWithReg_sub _ h12
end Part1B_Ghost334AndSingleBarrel6Step
end SingleBarrel8StepClean
end SharedScope
end
end SlimStageADepsD

noncomputable section BoothOpt_P4_10_TwoLoadHeldRowTrueSwap

section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option exponentiation.threshold 256
namespace BoothOpt_P4_10_TwoLoadHeldRowTrueSwap
attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup littleWedderburn
  Unitary.instCommGroupSubtypeMemSubmonoidUnitary
local instance (priority := 1000000) instNeZeroTwoPow4 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open Operator QProg Matrix Real HermitianMat
open SpecsAux.SpecMirror
open _root_.DynamicCircuit
open DynCircuitExt hiding czCircuit
open Circuit hiding TOFF T
open PrimitiveGate (TOFF T)
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open MeasureBranchHadamardSem (ket bitSign sqrtHalf ket_H matrix_ext_ket)
open FullSysCatSegmentBridge (disjointWires_concat_left)
open PosSlots24BranchConcrete
open PosSlots24PartnerMux288 hiding ite_pos ite_neg
open PosSlots24PartnerMuxZeroT123 hiding ite_pos ite_neg dite_pos dite_neg
open PosSlots24Barrel3Pass
open AnchorSwap0Split133
open MultiBankWStateRouter
open ParticleOneHotWState
open BoothOpt_StageBPartnerCoreShave (DiagCtxWG
  DiagCtxWGWritesAbove ctxShiftedPartnerFast ctxShiftedPartnerFast_writesAbove InvHoleShifted218
  rShiftedIdx17OfFin rShiftedIdx17Core rShiftedIdx17OfFin_zero rShiftedIdx17OfFin_anc
  rShiftedIdx17OfFin_part rComb133 rComb133_apply_lt rComb133_apply_ge selShiftedIdx17
  actPreservesShifted17_to_comb133Pres wSlot1Core_ofFin_val rAnchorIdx_ofFin_val_local
  rPartnerIdx_ofFin_val_local rElecSlot_ofFin_val_local)
/-- Unheld phase-kick tail on bits `K .. K + t - 1` (`444 * t` `T`, `TOFF = 0`). -/
noncomputable def dUnheldTailAux {Var : Type} {n mScr : ℕ}
    (K : ℕ) (hm : 75 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) :
    ∀ (t : ℕ), K + t ≤ 18 → DynamicCircuit Var n
  | 0, _ => .circuit .identity
  | t + 1, ht =>
      .seq (dUnheldTailAux K hm v rCore rMeas rScr hCS hMS t (by omega))
           (dKick1Bit218 hm v ⟨K + t, ht⟩ rCore rMeas rScr hCS hMS)
theorem dUnheldTailAux_count {Var : Type} {n mScr : ℕ}
    (K : ℕ) (hm : 75 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) :
    ∀ (t : ℕ) (ht : K + t ≤ 18),
      (dUnheldTailAux (Var := Var) K hm v rCore rMeas rScr hCS hMS t ht).count TOFF = 0 ∧
      (dUnheldTailAux (Var := Var) K hm v rCore rMeas rScr hCS hMS t ht).count T = 444 * t
  | 0, _ => ⟨rfl, rfl⟩
  | t + 1, ht => by
      dsimp only [dUnheldTailAux, DynamicCircuit.count]
      obtain ⟨h1, h2⟩ := dUnheldTailAux_count K hm v rCore rMeas rScr hCS hMS t (by omega)
      rw [h1, h2, dKick1Bit218_count_toff, dKick1Bit218_count_t]
      exact ⟨rfl, by omega⟩
theorem subspaceStep_dUnheldTailAux {Var : Type} [Fintype Var] [DecidableEq Var]
    {n mScr : ℕ} [NeZero (2 ^ n)] (K : ℕ) (hK : K ≤ 18) (hm : 75 ≤ mScr) (v : Var)
    (rCore : QRegister posCoreWires n) (rMeas : QRegister 18 n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) :
    ∀ (t : ℕ) (ht : K + t ≤ 18) {R : Operator (2 ^ n)},
      SupportedOn (InvHoleShifted218 hm rCore rScr) R →
      SubspaceStep ((uKickPrefix218 K hK rCore rMeas).1 * R)
        ((uKickPrefix218 (K + t) ht rCore rMeas).1 * R)
        (dUnheldTailAux K hm v rCore rMeas rScr hCS hMS t ht)
  | 0, ht, R, _ => by
      dsimp only [dUnheldTailAux]
      have hEq : uKickPrefix218 (K + 0) ht rCore rMeas = uKickPrefix218 K hK rCore rMeas := rfl
      rw [hEq]
      exact subspaceStep_congr_out
        (subspaceStep_of_circuit (Var := Var) ((uKickPrefix218 K hK rCore rMeas).1 * R) .identity)
        (by simp)
  | t + 1, ht, R, hSupp => by
      dsimp only [dUnheldTailAux]
      have ih := subspaceStep_dUnheldTailAux K hK hm v rCore rMeas rScr hCS hMS t (by omega) hSupp
      have hSuppPrev : SupportedOn (InvHoleShifted218 hm rCore rScr)
          ((uKickPrefix218 (K + t) (by omega) rCore rMeas).1 * R) :=
        supportedOn_diagSignUnitary_mul _ hSupp
      have sLast := subspaceStep_dKick1Bit218 hm v ⟨K + t, ht⟩ rCore rMeas rScr hCS hMS hSuppPrev
      refine subspaceStep_congr_out (ih.seq sLast) ?_
      have hEq : uKickPrefix218 (K + (t + 1)) ht rCore rMeas =
          uKickPrefix218 ((K + t) + 1) ht rCore rMeas := rfl
      rw [hEq, uKickPrefix218_succ, Submonoid.coe_mul, Matrix.mul_assoc]
theorem diagCtxWGWritesAbove_fwdBits_lt {M base : ℕ} :
    ∀ {K : DiagCtxWG M}, DiagCtxWGWritesAbove base K →
      ∀ (γ : BitAssignment M) (idx : Wire M), idx.val < base → K.fwdBits γ idx = γ idx
  | .hole, _, _, _, _ => rfl
  | .cliffConj c _, ⟨hc, hK⟩, γ, idx, hlt =>
      (diagCtxWGWritesAbove_fwdBits_lt hK (c.eval γ) idx hlt).trans (hc.eval_lt γ idx hlt)
  | .tempAnd _ _ anc _ _ _ _, ⟨hanc, hK⟩, γ, idx, hlt =>
      (diagCtxWGWritesAbove_fwdBits_lt hK _ idx hlt).trans
        (Function.update_of_ne (Fin.ne_of_val_ne (by omega)) _ _)
  | .wStateTree _ wIdx wOut _ _ _, ⟨hOut, hK⟩, γ, idx, hlt =>
      (diagCtxWGWritesAbove_fwdBits_lt hK _ idx hlt).trans
        (Function.update_of_ne (Fin.ne_of_val_ne (by
          have := hOut ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩; omega)) _ _)
  | .wStateTreeCohGate1 _ _ wIdx wOut _ _ _, ⟨hOut, hK⟩, γ, idx, hlt =>
      (diagCtxWGWritesAbove_fwdBits_lt hK _ idx hlt).trans
        (Function.update_of_ne (Fin.ne_of_val_ne (by
          have := hOut ⟨idxValD wIdx γ, idxValD_lt_two_pow wIdx γ⟩; omega)) _ _)
noncomputable def fwdFastBits {n mScr : ℕ} (hm : 116 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (β : BitAssignment n) : BitAssignment n :=
  let rComb := rComb133 hm rCore rScr hCS
  p2d_writeReg β rComb (ctxShiftedPartnerFast.fwdBits (fun idx ↦ β (rComb idx)))
theorem fwdFastBits_outside_scr116 {n mScr : ℕ} (hm : 116 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (β : BitAssignment n) (w : Wire n)
    (hw : ∀ k : Fin 116, w ≠ rScr ⟨k.val, by omega⟩) :
    fwdFastBits hm rCore rScr hCS β w = β w := by
  let rComb := rComb133 hm rCore rScr hCS
  dsimp only [fwdFastBits]
  by_cases hmem : w ∈ Set.range rComb.wires
  · obtain ⟨idx, rfl⟩ := hmem
    by_cases hlt : idx.val < 17
    · rw [p2d_writeReg_apply_reg]
      exact diagCtxWGWritesAbove_fwdBits_lt ctxShiftedPartnerFast_writesAbove
        (fun i ↦ β (rComb i)) idx hlt
    · have hge : 17 ≤ idx.val := by omega
      exact absurd (rComb133_apply_ge hm rCore rScr hCS idx hge)
        (hw ⟨idx.val - 17, by omega⟩)
  · exact p2d_writeReg_apply_of_not_mem _ _ _ _ hmem
theorem rShiftedIdx17OfFin_val_ge_3949 (idx : Fin 17) :
    3949 ≤ (rShiftedIdx17OfFin idx).val := by
  by_cases h0 : idx.val = 0
  · have hi : idx = ⟨0, by decide⟩ := Fin.ext h0
    rw [hi, rShiftedIdx17OfFin_zero, wSlot1Core_ofFin_val]
  · by_cases h9 : idx.val < 9
    · let a : Fin 8 := ⟨idx.val - 1, by omega⟩
      have hi : idx = ⟨1 + a.val, by omega⟩ := Fin.ext (by dsimp [a]; omega)
      rw [hi, rShiftedIdx17OfFin_anc a, rAnchorIdx_ofFin_val_local]
      omega
    · let b : Fin 8 := ⟨idx.val - 9, by omega⟩
      have hi : idx = ⟨9 + b.val, by omega⟩ := Fin.ext (by dsimp [b]; omega)
      rw [hi, rShiftedIdx17OfFin_part b, rPartnerIdx_ofFin_val_local]
      omega
theorem rElec3924_not_mem_rComb133 {n mScr : ℕ} (hm : 116 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (i : Fin 3924) :
    rElec3924 rCore i ∉ Set.range (rComb133 hm rCore rScr hCS).wires := by
  rintro ⟨idx, hidx⟩
  by_cases hlt : idx.val < 17
  · rw [rComb133_apply_lt hm rCore rScr hCS idx hlt] at hidx
    dsimp only [rShiftedIdx17Core, QRegister.compose_apply] at hidx
    rw [rElec3924, QRegister.slice_apply] at hidx
    have hv := congrArg Fin.val (rCore.wires.injective hidx)
    have hge := rShiftedIdx17OfFin_val_ge_3949 ⟨idx.val, hlt⟩
    dsimp only at hv
    have := i.isLt
    omega
  · rw [rComb133_apply_ge hm rCore rScr hCS idx (by omega)] at hidx
    rw [rElec3924, QRegister.slice_apply] at hidx
    exact hCS.ne _ _ hidx.symm
theorem uFwdFast_comm_H_outside_rComb {n mScr : ℕ} (hm : 116 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) (q : Wire n)
    (hq : q ∉ Set.range (rComb133 hm rCore rScr hCS).wires) :
    (Circuit.H q).eval * uFwdWG (rComb133 hm rCore rScr hCS) ctxShiftedPartnerFast =
      uFwdWG (rComb133 hm rCore rScr hCS) ctxShiftedPartnerFast * (Circuit.H q).eval := by
  let rComb := rComb133 hm rCore rScr hCS
  have hqScr : ∀ k : Fin 116, q ≠ rScr ⟨k.val, by omega⟩ := fun k heq ↦
    hq ⟨⟨17 + k.val, by omega⟩, by
      rw [rComb133_apply_ge hm rCore rScr hCS ⟨17 + k.val, by omega⟩ (by dsimp; omega)]
      exact (congrArg rScr.wires (Fin.ext (by dsimp; omega))).trans heq.symm⟩
  have hUpd : ∀ (β : BitAssignment n) (b : ZMod 2),
      fwdFastBits hm rCore rScr hCS (Function.update β q b) =
        Function.update (fwdFastBits hm rCore rScr hCS β) q b := fun β b ↦ by
    funext w
    by_cases hwq : w = q
    · subst w
      rw [Function.update_self, fwdFastBits_outside_scr116 hm rCore rScr hCS _ q hqScr,
          Function.update_self]
    · rw [Function.update_of_ne hwq]
      dsimp only [fwdFastBits]
      have hCombEq : (fun idx ↦ Function.update β q b (rComb idx)) = fun idx ↦ β (rComb idx) :=
        funext fun idx ↦ Function.update_of_ne (fun h ↦ hq ⟨idx, h⟩) _ _
      by_cases hwC : w ∈ Set.range rComb.wires
      · obtain ⟨idx, rfl⟩ := hwC
        rw [p2d_writeReg_apply_reg, p2d_writeReg_apply_reg, hCombEq]
      · rw[p2d_writeReg_apply_of_not_mem _ _ _ _ hwC,
          p2d_writeReg_apply_of_not_mem _ _ _ _ hwC, Function.update_of_ne hwq]
  apply Subtype.ext; apply matrix_ext_ket; intro β
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      uFwdWG_mulVec_ket, ket_H, ket_H, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul,
      uFwdWG_mulVec_ket, uFwdWG_mulVec_ket]
  change sqrtHalf • (ket (Function.update (fwdFastBits hm rCore rScr hCS β) q 0) + bitSign
    (fwdFastBits hm rCore rScr hCS β q) • ket (Function.update (fwdFastBits hm rCore rScr hCS
    β) q 1)) = sqrtHalf • (ket (fwdFastBits hm rCore rScr hCS (Function.update β q 0)) +
    bitSign (β q) • ket (fwdFastBits hm rCore rScr hCS (Function.update β q 1)))
  rw [fwdFastBits_outside_scr116 hm rCore rScr hCS β q hqScr, hUpd β 0, hUpd β 1]
theorem uFwdFast_comm_cHadReg_elec {n mScr : ℕ} (hm : 116 ≤ mScr)
    (rCore : QRegister posCoreWires n) (rScr : QRegister mScr n)
    (hCS : rCore.DisjointWires rScr) : (cHadReg (rElec3924 rCore)).eval * uFwdWG
    (rComb133 hm rCore rScr hCS) ctxShiftedPartnerFast = uFwdWG (rComb133 hm rCore rScr hCS)
    ctxShiftedPartnerFast * (cHadReg (rElec3924 rCore)).eval := cHadReg_comm_of_wire_comm
    (rElec3924 rCore) _ fun i ↦ uFwdFast_comm_H_outside_rComb hm rCore rScr hCS
    (rElec3924 rCore i) (rElec3924_not_mem_rComb133 hm rCore rScr hCS i)
theorem actPreservesShifted17_uLensSwap {kData : ℕ} (selCore : QRegister posCoreWires kData) :
    ActPreservesShifted17 selCore (uLensSwap (shiftedPartnerLens218 selCore)) := by
  let L := shiftedPartnerLens218 selCore
  intro x y hnz
  dsimp only [uLensSwap] at hnz
  rw [permUnitary_apply] at hnz
  have hxy : y = lensSwapEquiv L x := by
    by_contra hne; dsimp only [L] at hne; rw [ite_eq_right hne] at hnz; exact hnz rfl
  subst y
  obtain ⟨hD, _⟩ := Prod.mk.inj (extractPair_liftPairIdx (lensSwapPerm L) x)
  have hDeq : (selDataInAct kData).extractIndex (lensSwapEquiv L x) =
      L.updSlot ((selDataInAct kData).extractIndex x) ((selMeasInAct kData).extractIndex x) := by
    dsimp only [lensSwapEquiv]; rw [Equiv.ofBijective_apply]; exact hD
  change (selShiftedIdx17 selCore).extractIndex ((selDataInAct kData).extractIndex (lensSwapEquiv L
      x)) =
    (selShiftedIdx17 selCore).extractIndex ((selDataInAct kData).extractIndex x)
  rw [hDeq]
  let d := (selDataInAct kData).extractIndex x
  let m := (selMeasInAct kData).extractIndex x
  apply basisBits_inj; intro idx
  rw [QRegister.basisBits_extractIndex, QRegister.basisBits_extractIndex]
  dsimp only [selShiftedIdx17, QRegister.compose_apply, L, shiftedPartnerLens218]
  refine QRegister.basisBits_replaceIndex_of_not_mem (shiftedPartnerSlotReg selCore d)
    d m (selCore (rShiftedIdx17OfFin idx)) ?_
  rintro ⟨j, hj⟩
  dsimp only [shiftedPartnerSlotReg, QRegister.compose_apply] at hj
  have hv := congrArg Fin.val (selCore.wires.injective hj)
  rw [rElecSlot_ofFin_val_local] at hv
  have hge := rShiftedIdx17OfFin_val_ge_3949 idx
  have hs := (shiftedPartnerSlotFast (fun w ↦ basisBits kData d (selCore w))).isLt
  have hjlt := j.isLt
  omega
theorem uFwdFast_comm_uLensSwap {n kData mScr : ℕ} (hm : 116 ≤ mScr)
    (rData : QRegister kData n) (selCore : QRegister posCoreWires kData)
    (rMeas : QRegister 18 n) (rScr : QRegister mScr n) (hDM : rData.DisjointWires rMeas)
    (hDS : rData.DisjointWires rScr) (hMS : rMeas.DisjointWires rScr) : uFwdWG (rComb133 hm
    (rData.compose selCore) rScr (hDS.compose_left selCore)) ctxShiftedPartnerFast *
    (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore)) =
    (rData.concat rMeas hDM).embedUnitary (uLensSwap (shiftedPartnerLens218 selCore)) * uFwdWG
    (rComb133 hm (rData.compose selCore) rScr (hDS.compose_left selCore))
    ctxShiftedPartnerFast := by
  obtain ⟨hOut, hCombPres⟩ := actPreservesShifted17_to_comb133Pres hm rData selCore rMeas rScr
    hDM hDS hMS (actPreservesShifted17_uLensSwap selCore)
  exact uFwdWG_comm_embedUnitary (rData.concat rMeas hDM)
    (uLensSwap (shiftedPartnerLens218 selCore)) _ 17 hOut hCombPres
    ctxShiftedPartnerFast_writesAbove
theorem disjointWires_concat_right {n k₁ k₂ k₃ : ℕ} (r₁ : QRegister k₁ n)
    (r₂ : QRegister k₂ n) (r₃ : QRegister k₃ n) (h₂₃ : r₂.DisjointWires r₃)
    (h₁₂ : r₁.DisjointWires r₂) (h₁₃ : r₁.DisjointWires r₃) : r₁.DisjointWires
    (r₂.concat r₃ h₂₃) :=
      (QRegExt.disjointWires_symm
      (disjointWires_concat_left h₂₃ (QRegExt.disjointWires_symm h₁₂)
      (QRegExt.disjointWires_symm h₁₃)))
theorem actPreservesShifted17_uLensLoad {kData : ℕ} (selCore : QRegister posCoreWires kData) :
    ActPreservesShifted17 selCore (uLensLoad (shiftedPartnerLens218 selCore)) := by
  let L := shiftedPartnerLens218 selCore
  intro x y hnz
  dsimp only [uLensLoad] at hnz
  rw [permUnitary_apply] at hnz
  have hxy : y = lensLoadEquiv L x := by
    by_contra hne; dsimp only [L] at hne; rw [ite_eq_right hne] at hnz; exact hnz rfl
  subst y
  obtain ⟨hD, _⟩ := Prod.mk.inj (extractPair_liftPairIdx (lensLoadPerm L) x)
  have hDeq : (selDataInAct kData).extractIndex (lensLoadEquiv L x) =
      (selDataInAct kData).extractIndex x := by
    dsimp only [lensLoadEquiv]; rw [Equiv.ofBijective_apply]; exact hD
  change (selShiftedIdx17 selCore).extractIndex ((selDataInAct kData).extractIndex (lensLoadEquiv L
      x)) =
    (selShiftedIdx17 selCore).extractIndex ((selDataInAct kData).extractIndex x)
  rw [hDeq]
theorem uKickPrefix218_mul_cHadReg_elec_eq {n kData : ℕ} (rData : QRegister kData n)
    (selCore : QRegister posCoreWires kData) (rMeas : QRegister 18 n)
    (hDM : rData.DisjointWires rMeas) : uKickPrefix218 18 le_rfl (rData.compose selCore) rMeas
    * (cHadReg (rElec3924 (rData.compose selCore))).eval =
    (cHadReg (rElec3924 (rData.compose selCore))).eval * (rData.concat rMeas hDM).embedUnitary
    (uLensWrite (shiftedPartnerLens218 selCore)) := by
  let HE := (cHadReg (rElec3924 (rData.compose selCore))).eval
  let UK := uKickPrefix218 18 le_rfl (rData.compose selCore) rMeas
  calc UK * HE
      = (HE * HE) * UK * HE := by rw [cHadReg_eval_mul_self, one_mul]
    _ = HE * (HE * UK * HE) := by simp only [mul_assoc]
    _ = HE * (rData.concat rMeas hDM).embedUnitary (uLensWrite (shiftedPartnerLens218 selCore)) :=
        by
        rw [cHadReg_elec_conj_uKickPrefix218_eq_uLensWrite]
attribute [irreducible]
  dUnheldTailAux
end BoothOpt_P4_10_TwoLoadHeldRowTrueSwap
end
end BoothOpt_P4_10_TwoLoadHeldRowTrueSwap

noncomputable section Tier72bAndScheduleClosure
set_option exponentiation.threshold 2048
set_option maxRecDepth 4096
namespace Tier72bAndScheduleClosure
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator
open SpecsAux SpecsAux.SpecMirror
local instance (priority := 1000000) instNeZeroTwoPowXorForest128 (k : ℕ) : NeZero (2 ^ k) :=
    ⟨(Nat.two_pow_pos k).ne'⟩
-- ============================================================================
-- Section 1: Top-Level Constants & Stage-2 Tier Parameters
-- ============================================================================
def nonS3ChiralNano (W : ℕ) : ℕ :=
  match W with
  | 28 => 8302760
  | 29 => 4185305
  | 30 => 2126599
  | 31 => 1097252
  | 32 => 582580
  | 33 => 325245
  | _ => 8302760
end Tier72bAndScheduleClosure
end Tier72bAndScheduleClosure

noncomputable section Slot3BoothAndBarrelOpt

section
namespace Slot3BoothAndBarrelOpt
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 256
set_option maxRecDepth 4096
local instance (priority := 100) instNeZeroTwoPowBoothOptSub (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
noncomputable section
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator
open SpecsAux SpecsAux.SpecMirror
open Prod57BoothHoist (bitsVal_castSucc_split)
open Slot3Norm1s36CoreWideBooth (n1sOut32W411)
theorem bitsVal_fin1 (f : Fin 1 → ZMod 2) : bitsVal f = (f 0).val := by
  rw [bitsVal_castSucc_split]
  have h0 : bitsVal (fun j : Fin 0 ↦ f j.castSucc) = 0 := by simp [bitsVal]
  rw [h0, zero_add]
  change 1 * (f 0).val = (f 0).val
  exact one_mul _
theorem bitsVal_fin4 (f : Fin 4 → ZMod 2) :
    bitsVal f = (f 0).val + 2 * (f 1).val + 4 * (f 2).val + 8 * (f 3).val := by
  rw [bitsVal_castSucc_split, bitsVal_castSucc_split, bitsVal_castSucc_split, bitsVal_fin1]
  change (f 0).val + 2 * (f 1).val + 4 * (f 2).val + 8 * (f 3).val = _
  rfl
/-- Entry zero-accumulator invariant `∀ k : Fin 32, γ (n1sOut32W411 k) = 0`. -/
def zrOut32ZeroInv (γ : BitAssignment 411) : Prop := ∀ k : Fin 32, γ (n1sOut32W411 k) = 0
end
end Slot3BoothAndBarrelOpt
end
end Slot3BoothAndBarrelOpt

end QuantumComputation.Specs.StoppingPowerSolution
end
