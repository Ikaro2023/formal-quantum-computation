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

public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxKernelB

/-!
# Fast Checkpointed `T_16` Multi-Segment Helpers (`FindAllJohnsonRampKickMuxHiBase`)

Provides single-barrier `O(1)`-`curLen` `T_16` evaluators (`muxUltraIterFullT16Rkm`,
`muxUltraIterFullT16HiChk`, `rkmEvalT16UltraLo12`), cross-leaf checkpoint chaining
(`rkmChainFastIterT16`), and zero-substep multi-segment row stitching
(`rkmCheckRowFromWalks_sound`)
over `FindAllJohnsonRampKickMuxKernelB`.
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

open Real
open scoped Matrix NNRat NNReal ENNReal

/-- Non-negative `ℤ` constructor alias avoiding `OfNat` synthesis on data lists. -/
abbrev rkmP : ℕ → ℤ := Int.ofNat

/-- Negative `ℤ` constructor alias `-(n + 1)` avoiding `Neg` synthesis on data lists. -/
abbrev rkmN : ℕ → ℤ := Int.negSucc

/-- Definitional alias for `rkmEvalT16Lo12... = rowOut` in leaf trajectory theorems. -/
abbrev rkmLo12EqHi (m lTableMax r : ℕ) (lSegs tauSegs nsubSegs : List ℕ)
    (masks : List (List Bool)) (rowOut : List ℕ) : Prop :=
  rkmEvalT16Lo12 m lTableMax r lSegs tauSegs nsubSegs masks = rowOut

/-- Kernel-exposed conjunction of a `List Bool` for batched `decide +kernel` checks. -/
def rkmAllTrueF : List Bool → Bool
  | [] => true
  | b :: bs => bif b then rkmAllTrueF bs else false

/-- Pre-certified single-segment `(hbExp, vecIn, vecWalk)` witness for
  `rkmEvalT16FromWalks`. -/
structure RkmSegWalk where
  hbExp : List ℤ
  vecIn : List ℤ
  vecWalk : List ℤ

/-- GMP-forced `(m: ℤ) - (n: ℤ)` reducing both branches once. -/
def rkmForcedSubNatNat (m n : ℕ) : ℤ :=
  match Nat.sub n m with
  | 0 => primOfNatForced (Nat.sub m n)
  | k + 1 => Int.negSucc k

/-- GMP-forced integer addition reducing every branch before list-spine construction. -/
def rkmForcedIntAdd : ℤ → ℤ → ℤ
  | Int.ofNat m, Int.ofNat n => primOfNatForced (Nat.add m n)
  | Int.ofNat m, Int.negSucc n => rkmForcedSubNatNat m (Nat.add n 1)
  | Int.negSucc m, Int.ofNat n => rkmForcedSubNatNat n (Nat.add m 1)
  | Int.negSucc m, Int.negSucc n => primNegSuccForced (Nat.add (Nat.add m n) 1)

/-- Fused `highdStrictConsInt (muxRawIntAdd a b) xs` (`<= 1` `Nat.add 1` barrier per cell). -/
def rkmUltraAddCons (a b : ℤ) (xs : List ℤ) : List ℤ :=
  match rkmForcedIntAdd a b with
  | Int.ofNat v =>
    match xs with
    | [] => [Int.ofNat v]
    | h :: t => Int.ofNat v :: h :: t
  | Int.negSucc v =>
    match xs with
    | [] => [Int.negSucc v]
    | h :: t => Int.negSucc v :: h :: t

/-- Unforced `((m: ℤ) - (n: ℤ)).tdiv (Int.ofNat dNat)` (`0` intermediate WHNF barriers). -/
def rkmUltraSubNatTdiv (m n dNat : ℕ) : ℤ :=
  match Nat.sub n m with
  | 0 => Int.ofNat (Nat.div (Nat.sub m n) dNat)
  | k + 1 => muxRawNegOfNat (Nat.div (Nat.add k 1) dNat)

/-- Fused 4-arm `(a - b).tdiv (Int.ofNat dNat)` (`0` intermediate WHNF barriers). -/
def rkmUltraSubTdiv : ℤ → ℤ → ℕ → ℤ
  | Int.ofNat m, Int.ofNat n, dNat => rkmUltraSubNatTdiv m n dNat
  | Int.ofNat m, Int.negSucc n, dNat => Int.ofNat (Nat.div (Nat.add m (Nat.add n 1)) dNat)
  | Int.negSucc m, Int.ofNat n, dNat => muxRawNegOfNat (Nat.div (Nat.add (Nat.add m 1) n) dNat)
  | Int.negSucc m, Int.negSucc n, dNat => rkmUltraSubNatTdiv (Nat.add n 1) (Nat.add m 1) dNat

/-- Single-barrier `O(outLen)` `T_16` sliding-window stage. -/
def rkmUltraSlideLoopAux (dNat : ℕ) : ℕ → ℤ → List ℤ → List ℤ → List ℤ → List ℤ
  | 0, _, _, _, _ => []
  | rem + 1, prev, hb, vec, cur =>
    match hb with
    | b :: hbRest =>
      match vec with
      | v :: vTail =>
        match cur with
        | c0 :: cTail =>
          let c1 := match cTail with | cn :: _ => cn | [] => Int.ofNat 0
          let q := rkmUltraSubTdiv prev (muxRawIntMul b c1) dNat
          rkmUltraAddCons v q
            (rkmUltraSlideLoopAux dNat rem (muxRawIntMul b c0) hbRest vTail cTail)
        | [] =>
          let q := rkmUltraSubTdiv prev (muxRawIntMul b (Int.ofNat 0)) dNat
          rkmUltraAddCons v q
            (rkmUltraSlideLoopAux dNat rem (muxRawIntMul b (Int.ofNat 0)) hbRest vTail [])
      | [] =>
        match cur with
        | c0 :: cTail =>
          let c1 := match cTail with | cn :: _ => cn | [] => Int.ofNat 0
          let q := rkmUltraSubTdiv prev (muxRawIntMul b c1) dNat
          rkmUltraAddCons (Int.ofNat 0) q
            (rkmUltraSlideLoopAux dNat rem (muxRawIntMul b c0) hbRest [] cTail)
        | [] =>
          let q := rkmUltraSubTdiv prev (muxRawIntMul b (Int.ofNat 0)) dNat
          rkmUltraAddCons (Int.ofNat 0) q
            (rkmUltraSlideLoopAux dNat rem (muxRawIntMul b (Int.ofNat 0)) hbRest [] [])
    | [] =>
      let vHead := match vec with | v :: _ => v | [] => Int.ofNat 0
      let vTail := match vec with | _ :: vt => vt | [] => []
      let cTail := match cur with | _ :: ct => ct | [] => []
      rkmUltraAddCons vHead (muxRawIntTdivNat prev dNat)
        (rkmUltraSlideLoopAux dNat rem (Int.ofNat 0) [] vTail cTail)

/-- Advances active `T_16` support length by `1` up to `maxLen` in `O(1)`. -/
def rkmNextLen (maxLen curLen : ℕ) : ℕ :=
  highdNatMin maxLen (Nat.add curLen 1)

/-- Advances active `T_16` support length across `16` stages in `O(1)`. -/
def rkmNextLen16 (maxLen curLen : ℕ) : ℕ :=
  rkmNextLen maxLen (rkmNextLen maxLen (rkmNextLen maxLen (rkmNextLen maxLen
    (rkmNextLen maxLen (rkmNextLen maxLen (rkmNextLen maxLen (rkmNextLen maxLen
    (rkmNextLen maxLen (rkmNextLen maxLen (rkmNextLen maxLen (rkmNextLen maxLen
    (rkmNextLen maxLen (rkmNextLen maxLen (rkmNextLen maxLen
      (rkmNextLen maxLen curLen)))))))))))))))

/-- Single-barrier degree-`deg` `T_16` Horner stage with explicit `curLen`. -/
def rkmUltraHornerStage (deg maxLen curLen : ℕ) (hb vec cur : List ℤ) : List ℤ :=
  let nxtRaw := rkmNextLen maxLen curLen
  HighDForce.withForcedNat nxtRaw fun nxtLen =>
    let dRaw := Nat.mul deg wdScale
    HighDForce.withForcedNat dRaw fun dNat =>
      rkmUltraSlideLoopAux dNat nxtLen (Int.ofNat 0) hb vec cur

/-- Single-barrier `16`-stage `T_16` Horner step tracking `curLen` in `O(1)`. -/
def rkmUltraHornerT16Step (maxLen curLen : ℕ) (hb vec : List ℤ) : List ℤ :=
  HighDForce.withForcedNat (rkmNextLen maxLen curLen) fun l15 =>
  HighDForce.withForcedList (rkmUltraHornerStage 16 maxLen curLen hb vec vec) fun c15 =>
  HighDForce.withForcedNat (rkmNextLen maxLen l15) fun l14 =>
  HighDForce.withForcedList (rkmUltraHornerStage 15 maxLen l15 hb vec c15) fun c14 =>
  HighDForce.withForcedNat (rkmNextLen maxLen l14) fun l13 =>
  HighDForce.withForcedList (rkmUltraHornerStage 14 maxLen l14 hb vec c14) fun c13 =>
  HighDForce.withForcedNat (rkmNextLen maxLen l13) fun l12 =>
  HighDForce.withForcedList (rkmUltraHornerStage 13 maxLen l13 hb vec c13) fun c12 =>
  HighDForce.withForcedNat (rkmNextLen maxLen l12) fun l11 =>
  HighDForce.withForcedList (rkmUltraHornerStage 12 maxLen l12 hb vec c12) fun c11 =>
  HighDForce.withForcedNat (rkmNextLen maxLen l11) fun l10 =>
  HighDForce.withForcedList (rkmUltraHornerStage 11 maxLen l11 hb vec c11) fun c10 =>
  HighDForce.withForcedNat (rkmNextLen maxLen l10) fun l9 =>
  HighDForce.withForcedList (rkmUltraHornerStage 10 maxLen l10 hb vec c10) fun c9 =>
  HighDForce.withForcedNat (rkmNextLen maxLen l9) fun l8 =>
  HighDForce.withForcedList (rkmUltraHornerStage 9 maxLen l9 hb vec c9) fun c8 =>
  HighDForce.withForcedNat (rkmNextLen maxLen l8) fun l7 =>
  HighDForce.withForcedList (rkmUltraHornerStage 8 maxLen l8 hb vec c8) fun c7 =>
  HighDForce.withForcedNat (rkmNextLen maxLen l7) fun l6 =>
  HighDForce.withForcedList (rkmUltraHornerStage 7 maxLen l7 hb vec c7) fun c6 =>
  HighDForce.withForcedNat (rkmNextLen maxLen l6) fun l5 =>
  HighDForce.withForcedList (rkmUltraHornerStage 6 maxLen l6 hb vec c6) fun c5 =>
  HighDForce.withForcedNat (rkmNextLen maxLen l5) fun l4 =>
  HighDForce.withForcedList (rkmUltraHornerStage 5 maxLen l5 hb vec c5) fun c4 =>
  HighDForce.withForcedNat (rkmNextLen maxLen l4) fun l3 =>
  HighDForce.withForcedList (rkmUltraHornerStage 4 maxLen l4 hb vec c4) fun c3 =>
  HighDForce.withForcedNat (rkmNextLen maxLen l3) fun l2 =>
  HighDForce.withForcedList (rkmUltraHornerStage 3 maxLen l3 hb vec c3) fun c2 =>
  HighDForce.withForcedNat (rkmNextLen maxLen l2) fun l1 =>
  HighDForce.withForcedList (rkmUltraHornerStage 2 maxLen l2 hb vec c2) fun c1 =>
  rkmUltraHornerStage 1 maxLen l1 hb vec c1

/-- Single-barrier `nSub`-step full-band `T_16` iterator tracking `curLen` in `O(1)`. -/
def muxUltraIterFullT16Rkm : ℕ → ℕ → ℕ → List ℤ → List ℤ → List ℤ
  | 0, _, _, _, vec => vec
  | k + 1, maxLen, curLen, hb, vec =>
    let stepVec := rkmUltraHornerT16Step maxLen curLen hb vec
    HighDForce.withForcedList stepVec fun vecNext =>
      HighDForce.withForcedNat (rkmNextLen16 maxLen curLen) fun nextLen =>
        muxUltraIterFullT16Rkm k maxLen nextLen hb vecNext

/-- Bounded `steps`-substep `T_16` chunk checker with WHNF-forced `hb`, `vecIn`, and
  `vecOut`. -/
def muxUltraIterFullT16HiChk (steps tag maxLen : ℕ) (hb vecIn vecOut : List ℤ) : Bool :=
  let _ := tag
  HighDForce.withForcedList hb fun hbF =>
    HighDForce.withForcedList vecIn fun inF =>
      HighDForce.withForcedList vecOut fun outF =>
        HighDForce.withForcedNat (altIntLen inF) fun len0 =>
          muxIntListEq (muxUltraIterFullT16Rkm steps maxLen len0 hbF inF) outF

/-- Structural multi-segment `T_16` + `mask` loop backed by `muxUltraIterFullT16Rkm`. -/
def rkmEvalSegsUltraLoop (m lTableMax r : ℕ) :
    List ℕ → List ℕ → List ℕ → List (List Bool) → ℕ → ℕ → ℕ → List ℤ → (ℕ × ℕ × List ℤ)
  | [], tauRem, nsubRem, maskRem, _, dEnd, accPad, vec =>
    match tauRem, nsubRem, maskRem with
    | [], [], [] => (dEnd, accPad, vec)
    | _, _, _ => (0, 0, [])
  | lS :: lRest, tau9 :: tauRest, nSub :: nsubRest, mask :: maskRest, lPrev, _, accPad, vec =>
    let mEff := Nat.mul lS m
    let d := highdNatMin mEff r
    bif Bool.or (primNatBlt lS 1)
      (Bool.or (primNatBlt lS lPrev)
      (Bool.or (primNatBlt lTableMax lS)
      (Bool.or (primNatBlt mEff 1)
      (Bool.or (primNatBlt 8192 mEff)
      (Bool.or (primNatBlt d 1)
      (Bool.or (Nat.beq tau9 0)
      (Bool.or (primNatBlt 4000000000 tau9)
      (Bool.or (Nat.beq nSub 0)
      (Bool.or (primNatBlt 16384 nSub)
        (primNatBlt (Nat.add d 1) (rkmBoolListLen mask))))))))))) then
      (0, 0, [])
    else
      let hPtRaw := Nat.div (Nat.mul tau9 1000000) nSub
      HighDForce.withForcedNat hPtRaw fun hPt =>
        bif primNatBlt hPt 1 then (0, 0, [])
        else
          let maxBRaw := altMaxBHiFrom mEff r 0 d
          HighDForce.withForcedNat maxBRaw fun maxBHi15 =>
            let bCapHi15 := Nat.mul 2 maxBHi15
            let hgRaw := highdMulCeil15 (Nat.add 2 hPt) bCapHi15
            HighDForce.withForcedNat hgRaw fun hgHi15 =>
              bif Bool.or (primNatBlt 1500000000000000 hgHi15)
                  (Bool.not (altCheckHbTight mEff r 0 d)) then
                (0, 0, [])
              else
                let hgPow := altPow17Ceil15 hgHi15
                let truncPad15 :=
                  Nat.div (Nat.add 299999999999999 (Nat.mul nSub hgPow)) 300000000000000
                let bCapCeil := Nat.div (Nat.add 999999999999999 bCapHi15) wdScale
                let segPad := Nat.add (Nat.add truncPad15 256)
                  (Nat.mul nSub (Nat.add 256 (Nat.mul 10 bCapCeil)))
                let nextPadRaw := Nat.add accPad segPad
                HighDForce.withForcedNat nextPadRaw fun nextPad =>
                  bif Bool.or (Nat.beq nextPad 0)
                      (primNatBlt 100000000000000 nextPad) then
                    (0, 0, [])
                  else
                    let hbRaw := altBuildHbFrom mEff r hPt 0 d
                    HighDForce.withForcedList hbRaw fun hbPt =>
                      let wRaw := muxUltraIterFullT16Rkm nSub (Nat.add d 1)
                        (altIntLen vec) hbPt vec
                      HighDForce.withForcedList wRaw fun vWalk =>
                        let kRaw := rkmApplyMaskBits mask vWalk
                        HighDForce.withForcedList kRaw fun vNext =>
                          rkmEvalSegsUltraLoop m lTableMax r lRest tauRest nsubRest maskRest
                            lS d nextPad vNext
  | _, _, _, _, _, _, _, _ => (0, 0, [])

/-- Evaluates `rkmEvalT16Lo12` directly via `muxUltraIterFullT16Rkm` on bounded-coord rows. -/
def rkmEvalT16UltraLo12 (m lTableMax r : ℕ)
    (lSegs tauSegs nsubSegs : List ℕ) (masks : List (List Bool)) : List ℕ :=
  let nSegs := altListLen lSegs
  bif Bool.or (Nat.beq nSegs 0)
    (Bool.or (primNatBlt 8 nSegs)
    (Bool.or (primNatBlt r 2) (primNatBlt 1024 r))) then
    []
  else
    let res := rkmEvalSegsUltraLoop m lTableMax r lSegs tauSegs nsubSegs masks
      1 0 0 [Int.ofNat wdScale]
    match res with
    | (dEnd, accPad, vecFinal) =>
      bif Bool.or (Nat.beq dEnd 0) (Nat.beq accPad 0) then []
      else
        let padded := altPadRightInts (Nat.add dEnd 1) vecFinal
        match padded with
        | [] => []
        | _ :: tail => altVecTailToLo12 accPad tail

/-- Zero-substep multi-segment stitcher verifying `(hbExp, vecIn)` and substituting
  `vecWalk`. -/
def rkmEvalSegsWithWalks (m lTableMax r : ℕ) :
    List ℕ → List ℕ → List ℕ → List (List Bool) → List RkmSegWalk →
      ℕ → ℕ → ℕ → List ℤ → (ℕ × ℕ × List ℤ)
  | [], tauRem, nsubRem, maskRem, walkRem, _, dEnd, accPad, vec =>
    match tauRem, nsubRem, maskRem, walkRem with
    | [], [], [], [] => (dEnd, accPad, vec)
    | _, _, _, _ => (0, 0, [])
  | lS :: lRest, tau9 :: tauRest, nSub :: nsubRest, mask :: maskRest, w :: wRest,
      lPrev, _, accPad, vec =>
    let mEff := Nat.mul lS m
    let d := highdNatMin mEff r
    bif Bool.or (primNatBlt lS 1)
      (Bool.or (primNatBlt lS lPrev)
      (Bool.or (primNatBlt lTableMax lS)
      (Bool.or (primNatBlt mEff 1)
      (Bool.or (primNatBlt 8192 mEff)
      (Bool.or (primNatBlt d 1)
      (Bool.or (Nat.beq tau9 0)
      (Bool.or (primNatBlt 4000000000 tau9)
      (Bool.or (Nat.beq nSub 0)
      (Bool.or (primNatBlt 16384 nSub)
        (primNatBlt (Nat.add d 1) (rkmBoolListLen mask))))))))))) then
      (0, 0, [])
    else
      let hPtRaw := Nat.div (Nat.mul tau9 1000000) nSub
      HighDForce.withForcedNat hPtRaw fun hPt =>
        bif primNatBlt hPt 1 then (0, 0, [])
        else
          let maxBRaw := altMaxBHiFrom mEff r 0 d
          HighDForce.withForcedNat maxBRaw fun maxBHi15 =>
            let bCapHi15 := Nat.mul 2 maxBHi15
            let hgRaw := highdMulCeil15 (Nat.add 2 hPt) bCapHi15
            HighDForce.withForcedNat hgRaw fun hgHi15 =>
              bif Bool.or (primNatBlt 1500000000000000 hgHi15)
                  (Bool.not (altCheckHbTight mEff r 0 d)) then
                (0, 0, [])
              else
                let hgPow := altPow17Ceil15 hgHi15
                let truncPad15 :=
                  Nat.div (Nat.add 299999999999999 (Nat.mul nSub hgPow)) 300000000000000
                let bCapCeil := Nat.div (Nat.add 999999999999999 bCapHi15) wdScale
                let segPad := Nat.add (Nat.add truncPad15 256)
                  (Nat.mul nSub (Nat.add 256 (Nat.mul 10 bCapCeil)))
                let nextPadRaw := Nat.add accPad segPad
                HighDForce.withForcedNat nextPadRaw fun nextPad =>
                  bif Bool.or (Nat.beq nextPad 0)
                      (primNatBlt 100000000000000 nextPad) then
                    (0, 0, [])
                  else
                    let hbRaw := altBuildHbFrom mEff r hPt 0 d
                    HighDForce.withForcedList hbRaw fun hbPt =>
                      bif Bool.not (Bool.and (muxIntListEq hbPt w.hbExp)
                          (muxIntListEq vec w.vecIn)) then
                        (0, 0, [])
                      else
                        HighDForce.withForcedList w.vecWalk fun vWalk =>
                          let kRaw := rkmApplyMaskBits mask vWalk
                          HighDForce.withForcedList kRaw fun vNext =>
                            rkmEvalSegsWithWalks m lTableMax r lRest tauRest nsubRest
                              maskRest wRest lS d nextPad vNext
  | _, _, _, _, _, _, _, _, _ => (0, 0, [])

/-- Evaluates post-trajectory `rowLo12` from pre-certified segment walks `walks`. -/
def rkmEvalT16FromWalks (m lTableMax r : ℕ)
    (lSegs tauSegs nsubSegs : List ℕ) (masks : List (List Bool))
    (walks : List RkmSegWalk) : List ℕ :=
  let nSegs := altListLen lSegs
  bif Bool.or (Nat.beq nSegs 0)
    (Bool.or (primNatBlt 8 nSegs)
    (Bool.or (primNatBlt r 2) (primNatBlt 1024 r))) then
    []
  else
    let res := rkmEvalSegsWithWalks m lTableMax r lSegs tauSegs nsubSegs masks walks
      1 0 0 [Int.ofNat wdScale]
    match res with
    | (dEnd, accPad, vecFinal) =>
      bif Bool.or (Nat.beq dEnd 0) (Nat.beq accPad 0) then []
      else
        let padded := altPadRightInts (Nat.add dEnd 1) vecFinal
        match padded with
        | [] => []
        | _ :: tail => altVecTailToLo12 accPad tail

/-- Boolean row stitcher checking `rkmEvalT16FromWalks... = rowOut` in `O(d)` kernel steps. -/
def rkmCheckRowFromWalks (m lTableMax r : ℕ)
    (lSegs tauSegs nsubSegs : List ℕ) (masks : List (List Bool))
    (walks : List RkmSegWalk) (rowOut : List ℕ) : Bool :=
  bif primNatBlt (altListLen rowOut) 1 then false
  else muxNatListEq (rkmEvalT16FromWalks m lTableMax r lSegs tauSegs nsubSegs masks walks) rowOut

/-- Semantic soundness of pre-certified segment walk witnesses `walks`. -/
def RkmSegWalksSound (m r : ℕ) : List ℕ → List ℕ → List RkmSegWalk → Prop
  | [], [], [] => True
  | lS :: lRest, nSub :: nsubRest, w :: wRest =>
      muxFastIterFullT16 nSub (Nat.add (highdNatMin (Nat.mul lS m) r) 1)
        w.hbExp w.vecIn = w.vecWalk ∧
        RkmSegWalksSound m r lRest nsubRest wRest
  | _, _, _ => False

end

public section

open Real
open scoped Matrix NNRat NNReal ENNReal

private theorem rkmhi_cond_true {α : Type} (a b : α) : (bif true then a else b) = a := rfl
private theorem rkmhi_cond_false {α : Type} (a b : α) : (bif false then a else b) = b := rfl

/-- Unpacks the head and tail of a certified `rkmAllTrueF (b:: bs) = true` batch. -/
theorem rkmAllTrueF_cons {b : Bool} {bs : List Bool} (h : rkmAllTrueF (b :: bs) = true) :
    b = true ∧ rkmAllTrueF bs = true := by
  cases b with
  | false => exact Bool.noConfusion h
  | true => exact ⟨rfl, h⟩

private theorem rkmhi_strictConsInt_eq (x : ℤ) (xs : List ℤ) :
    highdStrictConsInt x xs = x :: xs := by
  cases x with
  | ofNat n =>
    change (match Nat.add 1 n with
      | 0 => match xs with | [] => [Int.ofNat 0] | h :: t => Int.ofNat 0 :: h :: t
      | v + 1 => match xs with | [] => [Int.ofNat v] | h :: t => Int.ofNat v :: h :: t) =
      Int.ofNat n :: xs
    rw [show Nat.add 1 n = n + 1 from Nat.one_add n]
    cases xs <;> rfl
  | negSucc n =>
    change (match Nat.add 1 n with
      | 0 => match xs with | [] => [Int.negSucc 0] | h :: t => Int.negSucc 0 :: h :: t
      | v + 1 => match xs with | [] => [Int.negSucc v] | h :: t => Int.negSucc v :: h :: t) =
      Int.negSucc n :: xs
    rw [show Nat.add 1 n = n + 1 from Nat.one_add n]
    cases xs <;> rfl

private theorem rkmhi_ofNatForced_eq (x : ℕ) : primOfNatForced x = Int.ofNat x := by
  simp [primOfNatForced, Nat.one_add]

private theorem rkmhi_negSuccForced_eq (x : ℕ) : primNegSuccForced x = Int.negSucc x := by
  simp [primNegSuccForced, Nat.one_add]

private theorem rkmhi_rawNeg_eq (x : ℕ) : muxRawNegOfNat x = primNegOfNat x := by
  cases x with
  | zero => rfl
  | succ k => simp [muxRawNegOfNat, primNegOfNat, primNegSuccForced, Nat.one_add]

private theorem rkmhi_rawMul_eq (a b : ℤ) : muxRawIntMul a b = primIntMul a b := by
  cases a <;> cases b <;>
    simp [muxRawIntMul, primIntMul, primOfNatForced, rkmhi_rawNeg_eq, Nat.one_add]

private theorem rkmhi_forcedSubNat_eq (m n : ℕ) :
    rkmForcedSubNatNat m n = muxRawSubNatNat m n := by
  unfold rkmForcedSubNatNat muxRawSubNatNat
  cases Nat.sub n m <;> simp [primOfNatForced, Nat.one_add]

private theorem rkmhi_forcedAdd_eq (a b : ℤ) : rkmForcedIntAdd a b = muxRawIntAdd a b := by
  cases a <;> cases b <;> simp only [rkmForcedIntAdd, muxRawIntAdd, rkmhi_forcedSubNat_eq]

private theorem rkmhi_ultraAddCons_eq (a b : ℤ) (xs : List ℤ) :
    rkmUltraAddCons a b xs = highdStrictConsInt (muxRawIntAdd a b) xs := by
  unfold rkmUltraAddCons
  rw [rkmhi_forcedAdd_eq, rkmhi_strictConsInt_eq]
  cases muxRawIntAdd a b <;> cases xs <;> rfl

private theorem rkmhi_ultraSubNatTdiv_eq (m n dNat : ℕ) :
    rkmUltraSubNatTdiv m n dNat = muxRawIntTdivNat (muxRawSubNatNat m n) dNat := by
  unfold rkmUltraSubNatTdiv muxRawSubNatNat
  cases Nat.sub n m <;> rfl

private theorem rkmhi_ultraSubTdiv_eq (a b : ℤ) (dNat : ℕ) :
    rkmUltraSubTdiv a b dNat = muxRawIntTdivNat (muxRawIntSub a b) dNat := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      cases n with
      | zero =>
        simp only [rkmUltraSubTdiv, rkmUltraSubNatTdiv, muxRawIntSub, muxRawIntNeg,
          muxRawNegOfNat, muxRawIntAdd, muxRawIntTdivNat, rkmhi_ofNatForced_eq,
          Nat.sub_eq, Nat.add_eq, Nat.zero_sub, Nat.sub_zero, Nat.add_zero]
      | succ k =>
        exact rkmhi_ultraSubNatTdiv_eq m (k + 1) dNat
    | negSucc n =>
      simp only [rkmUltraSubTdiv, muxRawIntSub, muxRawIntNeg, muxRawIntAdd,
        muxRawIntTdivNat, rkmhi_ofNatForced_eq, Nat.add_eq]
  | negSucc m =>
    cases b with
    | ofNat n =>
      cases n with
      | zero => rfl
      | succ k =>
        simp only [rkmUltraSubTdiv, muxRawIntSub, muxRawIntNeg, muxRawNegOfNat,
          muxRawIntAdd, rkmhi_negSuccForced_eq, muxRawIntTdivNat, Nat.add_eq]
        exact congrArg muxRawNegOfNat (congrArg (· / dNat) (by omega))
    | negSucc n =>
      simp only [rkmUltraSubTdiv, muxRawIntSub, muxRawIntNeg, rkmhi_ofNatForced_eq,
        muxRawIntAdd, rkmhi_ultraSubNatTdiv_eq, Nat.add_eq]

private theorem rkmhi_ultraSlideLoopAux_eq (dNat : ℕ) :
    ∀ (rem : ℕ) (prev : ℤ) (hb vec cur : List ℤ),
      rkmUltraSlideLoopAux dNat rem prev hb vec cur =
        muxFastSlideLoopAux dNat rem prev hb vec cur
  | 0, _, _, _, _ => rfl
  | rem + 1, prev, hb, vec, cur => by
    cases hb with
    | nil =>
      cases vec <;> cases cur <;>
        simp only [rkmUltraSlideLoopAux, muxFastSlideLoopAux, rkmhi_ultraAddCons_eq,
          rkmhi_ultraSlideLoopAux_eq dNat rem]
    | cons b hbRest =>
      cases vec with
      | nil =>
        cases cur with
        | nil =>
          simp only [rkmUltraSlideLoopAux, muxFastSlideLoopAux, rkmhi_ultraAddCons_eq,
            rkmhi_ultraSubTdiv_eq, rkmhi_rawMul_eq, rkmhi_ultraSlideLoopAux_eq dNat rem]
        | cons c0 cTail =>
          cases cTail <;>
            simp only [rkmUltraSlideLoopAux, muxFastSlideLoopAux, rkmhi_ultraAddCons_eq,
              rkmhi_ultraSubTdiv_eq, rkmhi_rawMul_eq, rkmhi_ultraSlideLoopAux_eq dNat rem]
      | cons v vTail =>
        cases cur with
        | nil =>
          simp only [rkmUltraSlideLoopAux, muxFastSlideLoopAux, rkmhi_ultraAddCons_eq,
            rkmhi_ultraSubTdiv_eq, rkmhi_rawMul_eq, rkmhi_ultraSlideLoopAux_eq dNat rem]
        | cons c0 cTail =>
          cases cTail <;>
            simp only [rkmUltraSlideLoopAux, muxFastSlideLoopAux, rkmhi_ultraAddCons_eq,
              rkmhi_ultraSubTdiv_eq, rkmhi_rawMul_eq, rkmhi_ultraSlideLoopAux_eq dNat rem]

private theorem rkmhi_ultraSlideLoopAux_fun_eq : rkmUltraSlideLoopAux = muxFastSlideLoopAux := by
  funext dNat rem prev hb vec cur
  exact rkmhi_ultraSlideLoopAux_eq dNat rem prev hb vec cur

private theorem rkmhi_len_slideLoop (dNat : ℕ) :
    ∀ (rem : ℕ) (prev : ℤ) (hb vec cur : List ℤ),
      altIntLen (muxFastSlideLoopAux dNat rem prev hb vec cur) = rem
  | 0, _, _, _, _ => rfl
  | rem + 1, prev, hb, vec, cur => by
    cases hb with
    | nil =>
      cases vec <;> cases cur <;>
        simp only [muxFastSlideLoopAux, rkmhi_strictConsInt_eq, altIntLen,
          rkmhi_len_slideLoop dNat rem]
    | cons b hbRest =>
      cases vec with
      | nil =>
        cases cur with
        | nil =>
          simp only [muxFastSlideLoopAux, rkmhi_strictConsInt_eq, altIntLen,
            rkmhi_len_slideLoop dNat rem]
        | cons c0 cTail =>
          cases cTail <;>
            simp only [muxFastSlideLoopAux, rkmhi_strictConsInt_eq, altIntLen,
              rkmhi_len_slideLoop dNat rem]
      | cons v vTail =>
        cases cur with
        | nil =>
          simp only [muxFastSlideLoopAux, rkmhi_strictConsInt_eq, altIntLen,
            rkmhi_len_slideLoop dNat rem]
        | cons c0 cTail =>
          cases cTail <;>
            simp only [muxFastSlideLoopAux, rkmhi_strictConsInt_eq, altIntLen,
              rkmhi_len_slideLoop dNat rem]

private theorem rkmhi_ultraHornerStage_eq (deg maxLen curLen : ℕ) (hb vec cur : List ℤ)
    (hl : altIntLen cur = curLen) :
    rkmUltraHornerStage deg maxLen curLen hb vec cur =
      muxFastHornerStage deg maxLen hb vec cur := by
  subst hl
  unfold rkmUltraHornerStage muxFastHornerStage rkmNextLen
  rw [rkmhi_ultraSlideLoopAux_fun_eq]

private theorem rkmhi_len_fastStage (deg maxLen : ℕ) (hb vec cur : List ℤ) :
    altIntLen (muxFastHornerStage deg maxLen hb vec cur) = rkmNextLen maxLen (altIntLen cur) := by
  unfold muxFastHornerStage rkmNextLen
  simp only [rkmb_forceNat_eq, rkmhi_len_slideLoop]

private theorem rkmhi_len_fastStep (maxLen : ℕ) (hb vec : List ℤ) :
    altIntLen (muxFastHornerT16Step maxLen hb vec) = rkmNextLen16 maxLen (altIntLen vec) := by
  unfold muxFastHornerT16Step rkmNextLen16
  simp only [rkmb_forceList_eq, rkmhi_len_fastStage]

private theorem rkmhi_ultraStage_step {α : Type} (deg maxLen curLen : ℕ)
    (hb vec cur : List ℤ) (kUltra : ℕ → List ℤ → α) (kFast : List ℤ → α)
    (hl : altIntLen cur = curLen)
    (hk : ∀ (cNext : List ℤ),
      altIntLen cNext = rkmNextLen maxLen curLen →
      kUltra (rkmNextLen maxLen curLen) cNext = kFast cNext) :
    (HighDForce.withForcedNat (rkmNextLen maxLen curLen) fun lNext =>
      HighDForce.withForcedList (rkmUltraHornerStage deg maxLen curLen hb vec cur)
        fun cNext => kUltra lNext cNext) =
    (HighDForce.withForcedList (muxFastHornerStage deg maxLen hb vec cur) kFast) := by
  rw [rkmb_forceNat_eq, rkmb_forceList_eq, rkmb_forceList_eq,
    rkmhi_ultraHornerStage_eq deg maxLen curLen hb vec cur hl]
  have hlen : altIntLen (muxFastHornerStage deg maxLen hb vec cur) =
      rkmNextLen maxLen curLen := by
    rw [rkmhi_len_fastStage, hl]
  exact hk _ hlen

private theorem rkmhi_ultraHornerT16Step_eq (maxLen curLen : ℕ) (hb vec : List ℤ)
    (hl : altIntLen vec = curLen) :
    rkmUltraHornerT16Step maxLen curLen hb vec = muxFastHornerT16Step maxLen hb vec := by
  unfold rkmUltraHornerT16Step muxFastHornerT16Step
  refine rkmhi_ultraStage_step 16 _ _ _ _ _ _ _ hl fun c15 hl15 => ?_
  refine rkmhi_ultraStage_step 15 _ _ _ _ _ _ _ hl15 fun c14 hl14 => ?_
  refine rkmhi_ultraStage_step 14 _ _ _ _ _ _ _ hl14 fun c13 hl13 => ?_
  refine rkmhi_ultraStage_step 13 _ _ _ _ _ _ _ hl13 fun c12 hl12 => ?_
  refine rkmhi_ultraStage_step 12 _ _ _ _ _ _ _ hl12 fun c11 hl11 => ?_
  refine rkmhi_ultraStage_step 11 _ _ _ _ _ _ _ hl11 fun c10 hl10 => ?_
  refine rkmhi_ultraStage_step 10 _ _ _ _ _ _ _ hl10 fun c9 hl9 => ?_
  refine rkmhi_ultraStage_step 9 _ _ _ _ _ _ _ hl9 fun c8 hl8 => ?_
  refine rkmhi_ultraStage_step 8 _ _ _ _ _ _ _ hl8 fun c7 hl7 => ?_
  refine rkmhi_ultraStage_step 7 _ _ _ _ _ _ _ hl7 fun c6 hl6 => ?_
  refine rkmhi_ultraStage_step 6 _ _ _ _ _ _ _ hl6 fun c5 hl5 => ?_
  refine rkmhi_ultraStage_step 5 _ _ _ _ _ _ _ hl5 fun c4 hl4 => ?_
  refine rkmhi_ultraStage_step 4 _ _ _ _ _ _ _ hl4 fun c3 hl3 => ?_
  refine rkmhi_ultraStage_step 3 _ _ _ _ _ _ _ hl3 fun c2 hl2 => ?_
  refine rkmhi_ultraStage_step 2 _ _ _ _ _ _ _ hl2 fun c1 hl1 => ?_
  exact rkmhi_ultraHornerStage_eq 1 maxLen _ hb vec c1 hl1

private theorem rkmhi_ultraIterFullT16_eq :
    ∀ (k maxLen curLen : ℕ) (hb vec : List ℤ),
      altIntLen vec = curLen →
      muxUltraIterFullT16Rkm k maxLen curLen hb vec = muxFastIterFullT16 k maxLen hb vec
  | 0, _, _, _, _, _ => rfl
  | k + 1, maxLen, curLen, hb, vec, hl => by
    unfold muxUltraIterFullT16Rkm muxFastIterFullT16
    rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceNat_eq,
      rkmhi_ultraHornerT16Step_eq maxLen curLen hb vec hl]
    apply rkmhi_ultraIterFullT16_eq k
    rw [rkmhi_len_fastStep, hl]

/-- Soundness of one `muxUltraIterFullT16HiChk` `decide +kernel` chunk certificate. -/
theorem muxUltraIterFullT16HiChk_sound {steps tag maxLen : ℕ} {hb vecIn vecOut : List ℤ}
    (h : muxUltraIterFullT16HiChk steps tag maxLen hb vecIn vecOut = true) :
    muxFastIterFullT16 steps maxLen hb vecIn = vecOut := by
  unfold muxUltraIterFullT16HiChk at h
  simp only [rkmb_forceList_eq, rkmb_forceNat_eq] at h
  rw [← rkmhi_ultraIterFullT16_eq steps maxLen (altIntLen vecIn) hb vecIn rfl]
  exact muxIntListEq_eq_true.mp h

/-- Additive step composition for `muxFastIterFullT16`. -/
theorem muxFastIterFullT16_add (k1 k2 maxLen : ℕ) (hb vec : List ℤ) :
    muxFastIterFullT16 (k1 + k2) maxLen hb vec =
      muxFastIterFullT16 k2 maxLen hb (muxFastIterFullT16 k1 maxLen hb vec) := by
  simp only [muxFastIterFullT16_eq, altIterFullT16_add]

/-- Transitive checkpoint chaining across independent depth-`1` leaf vectors. -/
theorem rkmChainFastIterT16 {k1 k2 kTot maxLen : ℕ} {hb1 hb2 v0 v1 v1' v2 : List ℤ}
    (hk : k1 + k2 = kTot)
    (hhb : muxIntListEq hb1 hb2 = true)
    (hv : muxIntListEq v1 v1' = true)
    (h1 : muxFastIterFullT16 k1 maxLen hb1 v0 = v1)
    (h2 : muxFastIterFullT16 k2 maxLen hb2 v1' = v2) :
    muxFastIterFullT16 kTot maxLen hb1 v0 = v2 := by
  subst hk
  rw [muxFastIterFullT16_add, h1, muxIntListEq_eq_true.mp hv,
    muxIntListEq_eq_true.mp hhb, h2]

private theorem rkmhi_evalSegsUltraLoop_eq (m lTableMax r : ℕ) :
    ∀ (lSegs tauSegs nsubSegs : List ℕ) (masks : List (List Bool))
      (lPrev dPrev accPad : ℕ) (vec : List ℤ),
      rkmEvalSegsUltraLoop m lTableMax r lSegs tauSegs nsubSegs masks lPrev dPrev accPad vec =
        rkmEvalSegsLoop m lTableMax r lSegs tauSegs nsubSegs masks lPrev dPrev accPad vec
  | [], _, _, _, _, _, _, _ => rfl
  | _ :: _, [], _, _, _, _, _, _ => rfl
  | _ :: _, _ :: _, [], _, _, _, _, _ => rfl
  | _ :: _, _ :: _, _ :: _, [], _, _, _, _ => rfl
  | lS :: lRest, tau9 :: tauRest, nSub :: nsubRest, mask :: maskRest, lPrev, dPrev, accPad,
      vec => by
    unfold rkmEvalSegsUltraLoop rkmEvalSegsLoop
    dsimp only
    refine congrArg (cond _ _) ?_
    refine congrArg (HighDForce.withForcedNat _) (funext fun hPt => ?_)
    refine congrArg (cond _ _) ?_
    refine congrArg (HighDForce.withForcedNat _) (funext fun maxBHi15 => ?_)
    refine congrArg (HighDForce.withForcedNat _) (funext fun hgHi15 => ?_)
    refine congrArg (cond _ _) ?_
    refine congrArg (HighDForce.withForcedNat _) (funext fun nextPad => ?_)
    refine congrArg (cond _ _) ?_
    refine congrArg (HighDForce.withForcedList _) (funext fun hbPt => ?_)
    rw [rkmhi_ultraIterFullT16_eq nSub _ (altIntLen vec) hbPt vec rfl]
    refine congrArg (HighDForce.withForcedList _) (funext fun vWalk => ?_)
    refine congrArg (HighDForce.withForcedList _) (funext fun vNext => ?_)
    exact rkmhi_evalSegsUltraLoop_eq m lTableMax r lRest tauRest nsubRest maskRest
      lS _ nextPad vNext

/-- Exact equality between `rkmEvalT16UltraLo12` and `rkmEvalT16Lo12`. -/
theorem rkmEvalT16UltraLo12_eq (m lTableMax r : ℕ)
    (lSegs tauSegs nsubSegs : List ℕ) (masks : List (List Bool)) :
    rkmEvalT16UltraLo12 m lTableMax r lSegs tauSegs nsubSegs masks =
      rkmEvalT16Lo12 m lTableMax r lSegs tauSegs nsubSegs masks := by
  unfold rkmEvalT16UltraLo12 rkmEvalT16Lo12
  dsimp only
  rw [rkmhi_evalSegsUltraLoop_eq]
  generalize rkmEvalSegsLoop m lTableMax r lSegs tauSegs nsubSegs masks
    1 0 0 [Int.ofNat wdScale] = res
  rcases res with ⟨dEnd, accPad, vecFinal⟩
  dsimp only
  generalize altPadRightInts (Nat.add dEnd 1) vecFinal = padded
  cases padded <;> rfl

/-- Converts a `rkmEvalT16UltraLo12` certificate into `rkmEvalT16Lo12`. -/
theorem rkmCertUltraRow {m lTableMax r : ℕ}
    {lSegs tauSegs nsubSegs : List ℕ} {masks : List (List Bool)} {rowOut : List ℕ}
    (h : muxNatListEq (rkmEvalT16UltraLo12 m lTableMax r lSegs tauSegs nsubSegs masks)
      rowOut = true) :
    rkmEvalT16Lo12 m lTableMax r lSegs tauSegs nsubSegs masks = rowOut := by
  rw [← rkmEvalT16UltraLo12_eq]
  exact muxNatListEq_eq_true.mp h

private theorem rkmhi_bif_zero_ne {b : Bool} {rest : ℕ × ℕ × List ℤ}
    {dOut padOut : ℕ} {vecOut : List ℤ}
    (h : (bif b then (0, 0, []) else rest) = (dOut, padOut, vecOut))
    (hd : dOut ≠ 0) : b = false ∧ rest = (dOut, padOut, vecOut) := by
  cases b with
  | false => exact ⟨rfl, h⟩
  | true => exact False.elim (hd (Prod.mk.inj h).1.symm)

private theorem rkmhi_not_and_eq_false {a b : Bool}
    (h : Bool.not (Bool.and a b) = false) : a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | exact Bool.noConfusion h

private theorem rkmhi_bif_nil_ne {b : Bool} {rest : List ℕ}
    (h : (bif b then [] else rest) ≠ []) : b = false := by
  cases b with
  | false => rfl
  | true => exact False.elim (h rfl)

private theorem rkmhi_evalSegsWithWalks_eq (m lTableMax r : ℕ) :
    ∀ (lSegs tauSegs nsubSegs : List ℕ) (masks : List (List Bool))
      (walks : List RkmSegWalk) (lPrev dPrev accPad dOut padOut : ℕ)
      (vec vecOut : List ℤ),
      RkmSegWalksSound m r lSegs nsubSegs walks →
      rkmEvalSegsWithWalks m lTableMax r lSegs tauSegs nsubSegs masks walks
        lPrev dPrev accPad vec = (dOut, padOut, vecOut) →
      dOut ≠ 0 →
      rkmEvalSegsLoop m lTableMax r lSegs tauSegs nsubSegs masks
        lPrev dPrev accPad vec = (dOut, padOut, vecOut)
  | [], tauSegs, nsubSegs, masks, walks, _, _, _, dOut, _, _, _, hws, hres, hdOut => by
    cases nsubSegs with
    | cons _ _ => exact False.elim hws
    | nil =>
      cases walks with
      | cons _ _ => exact False.elim hws
      | nil =>
        cases tauSegs with
        | cons _ _ => exact False.elim (hdOut (Prod.mk.inj hres).1.symm)
        | nil =>
          cases masks with
          | cons _ _ => exact False.elim (hdOut (Prod.mk.inj hres).1.symm)
          | nil => exact hres
  | lS :: lRest, tauSegs, nsubSegs, masks, walks, lPrev, dPrev, accPad, dOut, padOut,
      vec, vecOut, hws, hres, hdOut => by
    cases nsubSegs with
    | nil => exact False.elim hws
    | cons nSub nsubRest =>
      cases walks with
      | nil => exact False.elim hws
      | cons w wRest =>
        rcases hws with ⟨hw0, hwRest⟩
        cases tauSegs with
        | nil => exact False.elim (hdOut (Prod.mk.inj hres).1.symm)
        | cons tau9 tauRest =>
          cases masks with
          | nil => exact False.elim (hdOut (Prod.mk.inj hres).1.symm)
          | cons mask maskRest =>
            unfold rkmEvalSegsWithWalks at hres
            unfold rkmEvalSegsLoop
            simp only [rkmb_forceNat_eq, rkmb_forceList_eq] at hres ⊢
            rcases rkmhi_bif_zero_ne hres hdOut with ⟨hg1, hres⟩
            rw [hg1, rkmhi_cond_false]
            rcases rkmhi_bif_zero_ne hres hdOut with ⟨ghPt, hres⟩
            rw [ghPt, rkmhi_cond_false]
            rcases rkmhi_bif_zero_ne hres hdOut with ⟨ghg, hres⟩
            rw [ghg, rkmhi_cond_false]
            rcases rkmhi_bif_zero_ne hres hdOut with ⟨gnp, hres⟩
            rw [gnp, rkmhi_cond_false]
            rcases rkmhi_bif_zero_ne hres hdOut with ⟨geq, hres⟩
            rcases rkmhi_not_and_eq_false geq with ⟨hhb_b, hvec_b⟩
            have hwalk_eq :
                muxFastIterFullT16 nSub (Nat.add (highdNatMin (Nat.mul lS m) r) 1)
                  (altBuildHbFrom (Nat.mul lS m) r (Nat.div (Nat.mul tau9 1000000) nSub) 0
                    (highdNatMin (Nat.mul lS m) r)) vec = w.vecWalk := by
              rw [muxIntListEq_eq_true.mp hhb_b, muxIntListEq_eq_true.mp hvec_b]
              exact hw0
            rw [hwalk_eq]
            exact rkmhi_evalSegsWithWalks_eq m lTableMax r lRest tauRest nsubRest maskRest
              wRest lS (highdNatMin (Nat.mul lS m) r) _ dOut padOut _ vecOut hwRest hres hdOut

/-- Certifies `rkmEvalT16Lo12... = rowOut` from pre-certified segment walks
  `RkmSegWalksSound`
  and the `O(d)` row stitcher `rkmCheckRowFromWalks`. -/
theorem rkmCheckRowFromWalks_sound {m lTableMax r : ℕ}
    {lSegs tauSegs nsubSegs : List ℕ} {masks : List (List Bool)}
    {walks : List RkmSegWalk} {rowOut : List ℕ}
    (hws : RkmSegWalksSound m r lSegs nsubSegs walks)
    (hchk : rkmCheckRowFromWalks m lTableMax r lSegs tauSegs nsubSegs masks
      walks rowOut = true) :
    rkmEvalT16Lo12 m lTableMax r lSegs tauSegs nsubSegs masks = rowOut := by
  unfold rkmCheckRowFromWalks at hchk
  cases hlen : primNatBlt (altListLen rowOut) 1 with
  | true =>
    rw [hlen, rkmhi_cond_true] at hchk
    exact Bool.noConfusion hchk
  | false =>
    rw [hlen, rkmhi_cond_false] at hchk
    have hrow_ne : rowOut ≠ [] := by
      intro hnil; subst hnil; exact Bool.noConfusion hlen
    have heval : rkmEvalT16FromWalks m lTableMax r lSegs tauSegs nsubSegs masks walks = rowOut :=
      muxNatListEq_eq_true.mp hchk
    have hne : rkmEvalT16FromWalks m lTableMax r lSegs tauSegs nsubSegs masks walks ≠ [] := by
      rw [heval]; exact hrow_ne
    unfold rkmEvalT16FromWalks at heval hne
    unfold rkmEvalT16Lo12
    dsimp only at heval hne ⊢
    have ghdr := rkmhi_bif_nil_ne hne
    rw [ghdr, rkmhi_cond_false] at heval hne ⊢
    generalize hres : rkmEvalSegsWithWalks m lTableMax r lSegs tauSegs nsubSegs masks walks
      1 0 0 [Int.ofNat wdScale] = res at heval hne
    rcases res with ⟨dEnd, accPad, vecFinal⟩
    dsimp only at heval hne
    have gres := rkmhi_bif_nil_ne hne
    have hdEnd : dEnd ≠ 0 := by
      intro hd0; subst hd0; exact Bool.noConfusion gres
    have hloop := rkmhi_evalSegsWithWalks_eq m lTableMax r lSegs tauSegs nsubSegs masks walks
      1 0 0 dEnd accPad [Int.ofNat wdScale] vecFinal hws hres hdEnd
    rw [hloop]
    dsimp only
    rw [gres, rkmhi_cond_false] at heval ⊢
    generalize altPadRightInts (Nat.add dEnd 1) vecFinal = padded at heval ⊢
    cases padded <;> exact heval

end
end QuantumComputation.Specs.DickeSol
