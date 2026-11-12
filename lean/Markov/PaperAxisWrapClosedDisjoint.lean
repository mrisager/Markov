import Markov.PaperAxisNormalArcNoncrossing
import Markov.PaperAxisWrapGapDisjoint

/-! Genuine CLOSED-image disjointness of the joined wrap Q-arc and every
internal Q-arc. The two possible endpoint phase collisions are eliminated using
actual adjacent labels and the literal cyclic label law, not an assumed
endpoint-distinctness, matching, or classification field. -/

noncomputable section
open Set Topology
namespace Markov

/-- All closed wrap/internal Q-point values are distinct under the actual
all-phase projected-period injectivity property. -/
theorem paperAxisPeriodWrapSubarc_ne_internalGap_closed
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (i : Fin ((paperAxisPeriodCutPoints g hg a).card-1))
    (hfirst : 0 < i.val) (hlast : i.val+2 < (paperAxisPeriodCutPoints g hg a).card)
    (s t : unitInterval) :
    paperAxisPeriodWrapSubarc g hg a ha s ≠ paperAxisPeriodGapSubarc g hg a i t := by
  intro heq
  let L := modularClosedGeodesicPeriod g
  let x := paperAxisPeriodWrapParameter g hg a s
  let y := paperAxisPeriodGapParameter g hg a i t
  let z : paperIdealQuadrilateral := paperAxisPeriodWrapSubarc g hg a ha s
  have hL : 0 < L := modularClosedGeodesicPeriod_pos g hg
  have hx : x ∈ Icc (paperAxisWrapLeftTime g hg a) (paperAxisWrapRightTime g hg a) := by
    have hlt := lt_trans (paperAxisWrapTimes_straddle g hg a).1
      (paperAxisWrapTimes_straddle g hg a).2
    have hs0 := s.property.1
    have hs1 := s.property.2
    dsimp only [x, paperAxisPeriodWrapParameter]
    constructor <;> nlinarith
  have hy := paperAxisPeriodGapParameter_mem_closed_gap g hg a i t
  have hleftidx : paperAxisGapRightIndex g hg a (paperAxisFirstGapIndex g hg a) ≤
      paperAxisGapLeftIndex g hg a i := by
    change 0+1 ≤ i.val
    omega
  have hrightidx : paperAxisGapRightIndex g hg a i ≤
      paperAxisGapLeftIndex g hg a (paperAxisLastGapIndex g hg a) := by
    change i.val+1 ≤ (paperAxisPeriodCutPoints g hg a).card-2
    omega
  have hleft := (paperAxisPeriodCutTable g hg a).monotone hleftidx
  have hright := (paperAxisPeriodCutTable g hg a).monotone hrightidx
  have hlasttime : paperAxisPeriodCutTable g hg a
      (paperAxisGapLeftIndex g hg a (paperAxisLastGapIndex g hg a)) =
        paperAxisWrapLeftTime g hg a+L := by
    dsimp only [paperAxisWrapLeftTime, L]
    ring
  have hxy : x ≤ y := hx.2.trans (hleft.trans hy.1)
  have hyx : y ≤ x+L := by
    have hu := hy.2.trans hright
    rw [hlasttime] at hu
    linarith [hx.1]
  have hproj := congrArg (fun q : paperIdealQuadrilateral => modularTraceQuotientMk q) heq
  change modularTraceQuotientMk (paperAxisPeriodWrapSubarc g hg a ha s) =
    modularTraceQuotientMk (paperAxisPeriodGapSubarc g hg a i t) at hproj
  rw [paperAxisPeriodWrapSubarc_project, paperAxisPeriodGapSubarc_project] at hproj
  change modularTraceQuotientMk (modularHyperbolicAxis g hg x) =
    modularTraceQuotientMk (modularHyperbolicAxis g hg y) at hproj
  have hcases : x=y ∨ y=x+L := by
    by_cases hsame : x=y
    · exact Or.inl hsame
    by_cases hfull : y=x+L
    · exact Or.inr hfull
    have hlt : x < y := lt_of_le_of_ne hxy hsame
    have hless : y < x+L := lt_of_le_of_ne hyx hfull
    let b := (x+y-L)/2
    have hxb : x ∈ Ioo b (b+L) := by dsimp only [b]; constructor <;> linarith
    have hyb : y ∈ Ioo b (b+L) := by dsimp only [b]; constructor <;> linarith
    exact (hsame ((hproject b) hxb hyb hproj)).elim
  have hwact : paperAxisPeriodGapCellLabel g hg a (paperAxisFirstGapIndex g hg a) •
      (z:UpperHalfPlane) = modularHyperbolicAxis g hg x :=
    paperAxisPeriodWrapSubarc_smul g hg a ha s
  have hiact : paperAxisPeriodGapCellLabel g hg a i •
      (paperAxisPeriodGapSubarc g hg a i t : UpperHalfPlane) = modularHyperbolicAxis g hg y :=
    paperAxisPeriodGapSubarc_smul g hg a i t
  rcases hcases with hsame | hfull
  · have hlabels : paperAxisPeriodGapCellLabel g hg a (paperAxisFirstGapIndex g hg a) =
        paperAxisPeriodGapCellLabel g hg a i := by
      apply IsCancelSMul.right_cancel _ _ (z:UpperHalfPlane)
      calc
        _ = modularHyperbolicAxis g hg x := hwact
        _ = modularHyperbolicAxis g hg y := congrArg _ hsame
        _ = _ := hiact.symm
        _ = _ := congrArg (fun q : paperIdealQuadrilateral =>
          paperAxisPeriodGapCellLabel g hg a i • (q:UpperHalfPlane)) heq.symm
    have hends : paperAxisPeriodCutTable g hg a
        (paperAxisGapRightIndex g hg a (paperAxisFirstGapIndex g hg a)) =
          paperAxisPeriodCutTable g hg a (paperAxisGapLeftIndex g hg a i) := by
      apply le_antisymm hleft
      change paperAxisPeriodCutTable g hg a (paperAxisGapLeftIndex g hg a i) ≤
        paperAxisWrapRightTime g hg a
      have hyright : y ≤ paperAxisWrapRightTime g hg a := by rw [← hsame]; exact hx.2
      exact hy.1.trans hyright
    have hidx := congrArg Fin.val ((paperAxisPeriodCutTable g hg a).injective hends)
    have hadj : i.val=(paperAxisFirstGapIndex g hg a).val+1 := hidx.symm
    exact paperAxisPeriodGapCellLabel_adjacent_ne g hg a _ i hadj hlabels
  · have hlabels : paperAxisPeriodGapCellLabel g hg a i =
        paperAxisPeriodGapCellLabel g hg a (paperAxisLastGapIndex g hg a) := by
      apply IsCancelSMul.right_cancel _ _ (z:UpperHalfPlane)
      rw [paperAxisPeriodGapCellLabel_last_eq_period_mul_first g hg a ha]
      calc
        _ = paperAxisPeriodGapCellLabel g hg a i •
            (paperAxisPeriodGapSubarc g hg a i t : UpperHalfPlane) :=
          congrArg (fun q : paperIdealQuadrilateral =>
            paperAxisPeriodGapCellLabel g hg a i • (q:UpperHalfPlane)) heq
        _ = modularHyperbolicAxis g hg y := hiact
        _ = modularHyperbolicAxis g hg (x+L) := congrArg _ hfull
        _ = g • modularHyperbolicAxis g hg x := (modularHyperbolicAxis_action g hg x).symm
        _ = g • (paperAxisPeriodGapCellLabel g hg a (paperAxisFirstGapIndex g hg a) •
            (z:UpperHalfPlane)) := congrArg (fun w : UpperHalfPlane => g • w) hwact.symm
        _ = _ := (mul_smul _ _ _).symm
    have hends : paperAxisPeriodCutTable g hg a (paperAxisGapRightIndex g hg a i) =
        paperAxisPeriodCutTable g hg a (paperAxisGapLeftIndex g hg a (paperAxisLastGapIndex g hg a)) := by
      apply le_antisymm hright
      rw [hlasttime]
      calc
        paperAxisWrapLeftTime g hg a+L ≤ x+L := by linarith [hx.1]
        _ = y := hfull.symm
        _ ≤ _ := hy.2
    have hidx := congrArg Fin.val ((paperAxisPeriodCutTable g hg a).injective hends)
    have hadj : (paperAxisLastGapIndex g hg a).val=i.val+1 := hidx.symm
    exact paperAxisPeriodGapCellLabel_adjacent_ne g hg a i _ hadj hlabels

/-- The full CLOSED images of the genuine wrap arc and each actual internal
Q-subarc are disjoint, including both endpoint-collision phase cases. -/
theorem paperAxisPeriodWrapSubarc_internalGap_ranges_disjoint
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun r : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg r))
      (Ioo b (b+modularClosedGeodesicPeriod g)))
    (i : Fin ((paperAxisPeriodCutPoints g hg a).card-1))
    (hfirst : 0 < i.val) (hlast : i.val+2 < (paperAxisPeriodCutPoints g hg a).card) :
    Disjoint (range (paperAxisPeriodWrapSubarc g hg a ha)) (range (paperAxisPeriodGapSubarc g hg a i)) := by
  apply disjoint_left.mpr
  rintro q ⟨s, hs⟩ ⟨t, ht⟩
  exact paperAxisPeriodWrapSubarc_ne_internalGap_closed g hg a ha hproject i hfirst hlast s t (hs.trans ht.symm)

end Markov
