import Markov.PaperAxisCyclicCellLabels
import Markov.PaperCellSubarc
import Markov.PaperAxisNormalArcEndpoints

/-! The first and last off-side phase fragments are actually joined in their
common original cell, using the literal deck-period action and cyclic label.
No boundary matching or simple-class classification is assumed. -/
noncomputable section
open Set Topology
namespace Markov

theorem paperAxisPeriodCutPoints_three_le_of_off_sides
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg) :
    3 ≤ (paperAxisPeriodCutPoints g hg a).card := by
  by_contra hn
  have hc : (paperAxisPeriodCutPoints g hg a).card = 2 := by
    have := paperAxisPeriodCutPoints_two_le g hg a
    omega
  have hi : paperAxisLastGapIndex g hg a = paperAxisFirstGapIndex g hg a := by
    apply Fin.ext
    simp only [paperAxisLastGapIndex, paperAxisFirstGapIndex, hc]
  have hw := paperAxisPeriodGapCellLabel_last_eq_period_mul_first g hg a ha
  rw [hi] at hw
  have he : g * paperAxisPeriodGapCellLabel g hg a (paperAxisFirstGapIndex g hg a) =
      1 * paperAxisPeriodGapCellLabel g hg a (paperAxisFirstGapIndex g hg a) := by
    simpa only [one_mul] using hw.symm
  have hg1 : g = 1 := mul_right_cancel he
  have hx := modularHyperbolicAxis_action g hg a
  have hgaction (z : UpperHalfPlane) : g • z = z := by rw [hg1, one_smul]
  rw [hgaction] at hx
  have htime := (modularHyperbolicAxis_isometry g hg).injective hx
  have := modularClosedGeodesicPeriod_pos g hg
  linarith

def paperAxisWrapLeftTime (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) : ℝ :=
  paperAxisPeriodCutTable g hg a
    (paperAxisGapLeftIndex g hg a (paperAxisLastGapIndex g hg a)) -
      modularClosedGeodesicPeriod g

def paperAxisWrapRightTime (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) : ℝ :=
  paperAxisPeriodCutTable g hg a
    (paperAxisGapRightIndex g hg a (paperAxisFirstGapIndex g hg a))

private theorem wrap_first_left (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) :
    paperAxisPeriodCutTable g hg a
      (paperAxisGapLeftIndex g hg a (paperAxisFirstGapIndex g hg a)) = a :=
  (paperAxisPeriodCutTable_endpoints g hg a).1

private theorem wrap_last_right (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) :
    paperAxisPeriodCutTable g hg a
      (paperAxisGapRightIndex g hg a (paperAxisLastGapIndex g hg a)) =
        a + modularClosedGeodesicPeriod g := by
  have hi : paperAxisGapRightIndex g hg a (paperAxisLastGapIndex g hg a) =
      ⟨(paperAxisPeriodCutPoints g hg a).card-1,
        Nat.sub_lt (paperAxisPeriodCutPoints_card_pos g hg a) (by decide)⟩ := by
    apply Fin.ext
    have := paperAxisPeriodCutPoints_two_le g hg a
    change (paperAxisPeriodCutPoints g hg a).card-2+1 =
      (paperAxisPeriodCutPoints g hg a).card-1
    omega
  rw [hi]
  exact (paperAxisPeriodCutTable_endpoints g hg a).2

theorem paperAxisWrapTimes_straddle (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ) :
    paperAxisWrapLeftTime g hg a < a ∧ a < paperAxisWrapRightTime g hg a := by
  have hl := nonempty_Ioo.mp (paperAxisPeriodCutTable_gap_nonempty g hg a
    (paperAxisGapLeftIndex g hg a (paperAxisLastGapIndex g hg a))
    (paperAxisGapRightIndex g hg a (paperAxisLastGapIndex g hg a)) rfl)
  have hr := nonempty_Ioo.mp (paperAxisPeriodCutTable_gap_nonempty g hg a
    (paperAxisGapLeftIndex g hg a (paperAxisFirstGapIndex g hg a))
    (paperAxisGapRightIndex g hg a (paperAxisFirstGapIndex g hg a)) rfl)
  rw [wrap_last_right] at hl
  rw [wrap_first_left] at hr
  constructor
  · change _ - modularClosedGeodesicPeriod g < a
    linarith
  · exact hr

private theorem wrap_start_strict (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) :
    modularHyperbolicAxis g hg a ∈
      (fun z : UpperHalfPlane =>
        paperAxisPeriodGapCellLabel g hg a (paperAxisFirstGapIndex g hg a) • z) ''
          paperIdealQuadrilateralStrictRegion := by
  obtain ⟨δ,hδ,_⟩ := paperStrictCell_existsUnique_of_off_sides
    (modularHyperbolicAxis g hg a) (fun δ k h => ha ⟨δ,k,h⟩)
  have hf := (paperAxisPeriodGapCellLabel_spec g hg a (paperAxisFirstGapIndex g hg a)).2 a
  have hclosed : modularHyperbolicAxis g hg a ∈
      (fun z : UpperHalfPlane =>
        paperAxisPeriodGapCellLabel g hg a (paperAxisFirstGapIndex g hg a) • z) ''
          paperIdealQuadrilateral := by
    apply hf
    rw [wrap_first_left]
    exact ⟨le_rfl,(paperAxisWrapTimes_straddle g hg a).2.le⟩
  have he := paperStrictCell_label_unique δ _ _ hδ hclosed
  rwa [← he]

theorem paperAxisWrapInterval_cell (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) :
    (∀ t ∈ Icc (paperAxisWrapLeftTime g hg a) (paperAxisWrapRightTime g hg a),
      modularHyperbolicAxis g hg t ∈
        (fun z : UpperHalfPlane =>
          paperAxisPeriodGapCellLabel g hg a (paperAxisFirstGapIndex g hg a) • z) ''
            paperIdealQuadrilateral) ∧
    (∀ t ∈ Ioo (paperAxisWrapLeftTime g hg a) (paperAxisWrapRightTime g hg a),
      modularHyperbolicAxis g hg t ∈
        (fun z : UpperHalfPlane =>
          paperAxisPeriodGapCellLabel g hg a (paperAxisFirstGapIndex g hg a) • z) ''
            paperIdealQuadrilateralStrictRegion) := by
  let δ := paperAxisPeriodGapCellLabel g hg a (paperAxisFirstGapIndex g hg a)
  let ε := paperAxisPeriodGapCellLabel g hg a (paperAxisLastGapIndex g hg a)
  have hw : ε = g*δ := paperAxisPeriodGapCellLabel_last_eq_period_mul_first g hg a ha
  have htransport : ∀ z : UpperHalfPlane, ∀ t : ℝ,
      ε • z = modularHyperbolicAxis g hg (t+modularClosedGeodesicPeriod g) →
      δ • z = modularHyperbolicAxis g hg t := by
    intro z t he
    apply (modularTraceSubgroup_isometry g).injective
    calc
      g • (δ • z) = ε • z := by rw [← mul_smul, ← hw]
      _ = modularHyperbolicAxis g hg (t+modularClosedGeodesicPeriod g) := he
      _ = g • modularHyperbolicAxis g hg t := (modularHyperbolicAxis_action g hg t).symm
  constructor
  · intro t ht
    by_cases hta : t ≤ a
    · have hm : t+modularClosedGeodesicPeriod g ∈
          Icc (paperAxisPeriodCutTable g hg a
            (paperAxisGapLeftIndex g hg a (paperAxisLastGapIndex g hg a)))
            (paperAxisPeriodCutTable g hg a
              (paperAxisGapRightIndex g hg a (paperAxisLastGapIndex g hg a))) := by
        rw [wrap_last_right]
        have hl : paperAxisPeriodCutTable g hg a
            (paperAxisGapLeftIndex g hg a (paperAxisLastGapIndex g hg a)) -
              modularClosedGeodesicPeriod g ≤ t := ht.1
        constructor <;> linarith
      obtain ⟨z,hz,he⟩ := (paperAxisPeriodGapCellLabel_spec g hg a
        (paperAxisLastGapIndex g hg a)).2 _ hm
      exact ⟨z,hz,htransport z t he⟩
    · apply (paperAxisPeriodGapCellLabel_spec g hg a (paperAxisFirstGapIndex g hg a)).2
      rw [wrap_first_left]
      exact ⟨(lt_of_not_ge hta).le,ht.2⟩
  · intro t ht
    rcases lt_trichotomy t a with hta | hta | hat
    · have hm : t+modularClosedGeodesicPeriod g ∈
          Ioo (paperAxisPeriodCutTable g hg a
            (paperAxisGapLeftIndex g hg a (paperAxisLastGapIndex g hg a)))
            (paperAxisPeriodCutTable g hg a
              (paperAxisGapRightIndex g hg a (paperAxisLastGapIndex g hg a))) := by
        rw [wrap_last_right]
        have hl : paperAxisPeriodCutTable g hg a
            (paperAxisGapLeftIndex g hg a (paperAxisLastGapIndex g hg a)) -
              modularClosedGeodesicPeriod g < t := ht.1
        constructor <;> linarith
      obtain ⟨z,hz,he⟩ := (paperAxisPeriodGapCellLabel_spec g hg a
        (paperAxisLastGapIndex g hg a)).1 _ hm
      exact ⟨z,hz,htransport z t he⟩
    · simpa only [hta] using wrap_start_strict g hg a ha
    · apply (paperAxisPeriodGapCellLabel_spec g hg a (paperAxisFirstGapIndex g hg a)).1
      rw [wrap_first_left]
      exact ⟨hat,ht.2⟩

theorem paperAxisWrapTimes_sideCuts (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) :
    paperAxisWrapLeftTime g hg a ∈ paperAxisSideCuts g hg ∧
      paperAxisWrapRightTime g hg a ∈ paperAxisSideCuts g hg := by
  have hc := paperAxisPeriodCutPoints_three_le_of_off_sides g hg a ha
  constructor
  · apply (paperAxisSideCuts_period_iff g hg (paperAxisWrapLeftTime g hg a)).mp
    have hh := paperAxisPeriodCutTable_internal_mem_sideCuts g hg a
      (paperAxisGapLeftIndex g hg a (paperAxisLastGapIndex g hg a))
      (by change 0 < (paperAxisPeriodCutPoints g hg a).card-2; omega)
      (by change (paperAxisPeriodCutPoints g hg a).card-2+1 <
        (paperAxisPeriodCutPoints g hg a).card; omega)
    simpa only [paperAxisWrapLeftTime, sub_add_cancel] using hh
  · apply paperAxisPeriodCutTable_internal_mem_sideCuts
    · change 0 < 0+1
      omega
    · change 0+1+1 < (paperAxisPeriodCutPoints g hg a).card
      omega

/-- The two phase fragments form one actual Q-valued path crossing the base
phase in its genuine strict interior. Its endpoints are actual side cuts. -/
def paperAxisPeriodWrapSubarc (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) :=
  paperCellSubarc (modularHyperbolicAxis g hg)
    (modularHyperbolicAxis_isometry g hg).continuous
    (paperAxisWrapLeftTime g hg a) (paperAxisWrapRightTime g hg a)
    (lt_trans (paperAxisWrapTimes_straddle g hg a).1 (paperAxisWrapTimes_straddle g hg a).2)
    (paperAxisPeriodGapCellLabel g hg a (paperAxisFirstGapIndex g hg a))
    (paperAxisWrapInterval_cell g hg a ha).1

theorem paperAxisPeriodWrapSubarc_smul (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (s : unitInterval) :
    paperAxisPeriodGapCellLabel g hg a (paperAxisFirstGapIndex g hg a) •
      (paperAxisPeriodWrapSubarc g hg a ha s : UpperHalfPlane) =
        modularHyperbolicAxis g hg (paperAxisWrapLeftTime g hg a +
          (paperAxisWrapRightTime g hg a-paperAxisWrapLeftTime g hg a)*(s:ℝ)) :=
  paperCellSubarc_smul _ _ _ _ _ _ _ s

theorem paperAxisPeriodWrapSubarc_project (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (s : unitInterval) :
    modularTraceQuotientMk (paperAxisPeriodWrapSubarc g hg a ha s) =
      modularTraceQuotientMk (modularHyperbolicAxis g hg
        (paperAxisWrapLeftTime g hg a +
          (paperAxisWrapRightTime g hg a-paperAxisWrapLeftTime g hg a)*(s:ℝ))) :=
  paperCellSubarc_project _ _ _ _ _ _ _ s

theorem paperAxisPeriodWrapSubarc_isClosedEmbedding (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) :
    IsClosedEmbedding (paperAxisPeriodWrapSubarc g hg a ha) :=
  paperCellSubarc_isClosedEmbedding_of_isometry _ (modularHyperbolicAxis_isometry g hg)
    _ _ _ _ _

theorem paperAxisPeriodWrapSubarc_strict (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (s : unitInterval)
    (hs0 : 0 < (s:ℝ)) (hs1 : (s:ℝ) < 1) :
    (paperAxisPeriodWrapSubarc g hg a ha s : UpperHalfPlane) ∈
      paperIdealQuadrilateralStrictRegion :=
  paperCellSubarc_strict_of_interior _ _ _ _ _ _ _
    (paperAxisWrapInterval_cell g hg a ha).2 s hs0 hs1

theorem paperAxisPeriodWrapSubarc_endpoint_sides (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) :
    ∃ k l : Fin 4, k ≠ l ∧
      (paperAxisPeriodWrapSubarc g hg a ha 0 : UpperHalfPlane) ∈ paperQuadrilateralGeodesicSide k ∧
      (paperAxisPeriodWrapSubarc g hg a ha 1 : UpperHalfPlane) ∈ paperQuadrilateralGeodesicSide l ∧
      (∀ k', (paperAxisPeriodWrapSubarc g hg a ha 0 : UpperHalfPlane) ∈
        paperQuadrilateralGeodesicSide k' → k' = k) ∧
      (∀ l', (paperAxisPeriodWrapSubarc g hg a ha 1 : UpperHalfPlane) ∈
        paperQuadrilateralGeodesicSide l' → l' = l) := by
  let δ := paperAxisPeriodGapCellLabel g hg a (paperAxisFirstGapIndex g hg a)
  have hl : δ • (paperAxisPeriodWrapSubarc g hg a ha 0 : UpperHalfPlane) =
      modularHyperbolicAxis g hg (paperAxisWrapLeftTime g hg a) := by
    simpa only [show ((0:unitInterval):ℝ)=0 from rfl, mul_zero, add_zero] using
      paperAxisPeriodWrapSubarc_smul g hg a ha 0
  have hr : δ • (paperAxisPeriodWrapSubarc g hg a ha 1 : UpperHalfPlane) =
      modularHyperbolicAxis g hg (paperAxisWrapRightTime g hg a) := by
    simpa only [show ((1:unitInterval):ℝ)=1 from rfl, mul_one, add_sub_cancel] using
      paperAxisPeriodWrapSubarc_smul g hg a ha 1
  have hf0 : (paperAxisPeriodWrapSubarc g hg a ha 0 : UpperHalfPlane) ∈
      frontier paperIdealQuadrilateral := by
    obtain ⟨ε,k,hk⟩ := (paperAxisWrapTimes_sideCuts g hg a ha).1
    apply paperQuadrilateral_point_frontier_of_translated_side
      (paperAxisPeriodWrapSubarc g hg a ha 0) δ ε k
    rw [hl]
    exact hk
  have hf1 : (paperAxisPeriodWrapSubarc g hg a ha 1 : UpperHalfPlane) ∈
      frontier paperIdealQuadrilateral := by
    obtain ⟨ε,k,hk⟩ := (paperAxisWrapTimes_sideCuts g hg a ha).2
    apply paperQuadrilateral_point_frontier_of_translated_side
      (paperAxisPeriodWrapSubarc g hg a ha 1) δ ε k
    rw [hr]
    exact hk
  obtain ⟨k,hk,hku⟩ := paperQuadrilateral_frontier_existsUnique_side _ hf0
  obtain ⟨l,hll,hlu⟩ := paperQuadrilateral_frontier_existsUnique_side _ hf1
  refine ⟨k,l,?_,hk,hll,hku,hlu⟩
  intro hkl
  have he := modularHyperbolicAxis_paper_side_cut_subsingleton g hg δ k
    ⟨paperAxisPeriodWrapSubarc g hg a ha 0,hk,hl⟩
    ⟨paperAxisPeriodWrapSubarc g hg a ha 1,hkl ▸ hll,hr⟩
  exact (lt_trans (paperAxisWrapTimes_straddle g hg a).1
    (paperAxisWrapTimes_straddle g hg a).2).ne he

end Markov
