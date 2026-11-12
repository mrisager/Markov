import Markov.PaperAxisProperArcFamily
import Markov.PaperAxisWrapGapDisjoint

/-! Actual pairwise disjoint open images and cyclic quotient-endpoint gluing
for the exact finite proper-Q arc family. No endpoint ordering is claimed. -/
noncomputable section
open Set Topology
namespace Markov

private def properGluingGap (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : paperAxisProperArcIndex g hg a) :
    Fin ((paperAxisPeriodCutPoints g hg a).card - 1) :=
  ⟨i.val, by have := i.isLt; omega⟩

/-- Distinct members of the full proper family have disjoint actual open Q
images, including the joined wrap member. Actual period injectivity is explicit. -/
theorem paperAxisProperArc_interiors_disjoint
    (g : modularTraceSubgroup) (hg : 2 < |(g.val : IntMatrixTwo).trace|)
    (a : ℝ) (ha : a ∉ paperAxisSideCuts g hg)
    (hproject : ∀ b : ℝ, Set.InjOn
      (fun t : ℝ => modularTraceQuotientMk (modularHyperbolicAxis g hg t))
      (Ioo b (b + modularClosedGeodesicPeriod g)))
    (i j : paperAxisProperArcIndex g hg a) (hij : i ≠ j) :
    Disjoint ((paperAxisProperArc g hg a ha i) '' Ioo (0 : unitInterval) 1)
      ((paperAxisProperArc g hg a ha j) '' Ioo (0 : unitInterval) 1) := by
  have internal (k : paperAxisProperArcIndex g hg a) (hk : k.val ≠ 0) :
      0 < (properGluingGap g hg a k).val ∧
      (properGluingGap g hg a k).val + 2 < (paperAxisPeriodCutPoints g hg a).card := by
    have := k.isLt
    change 0 < k.val ∧ k.val + 2 < (paperAxisPeriodCutPoints g hg a).card
    omega
  by_cases hi : i.val = 0
  · have hj : j.val ≠ 0 := by
      intro hj
      exact hij (Fin.ext (hi.trans hj.symm))
    have hs := paperAxisPeriodWrapSubarc_internalGap_interiors_disjoint
      g hg a ha hproject (properGluingGap g hg a j) (internal j hj).1 (internal j hj).2
    simpa only [paperAxisProperArc, if_pos hi, if_neg hj] using hs
  · by_cases hj : j.val = 0
    · have hs := paperAxisPeriodWrapSubarc_internalGap_interiors_disjoint
        g hg a ha hproject (properGluingGap g hg a i) (internal i hi).1 (internal i hi).2
      simpa only [paperAxisProperArc, if_neg hi, if_pos hj] using hs.symm
    · have hne : properGluingGap g hg a i ≠ properGluingGap g hg a j := by
        intro he
        have hv : i.val = j.val := congrArg
          (fun k : Fin ((paperAxisPeriodCutPoints g hg a).card - 1) => k.val) he
        exact hij (Fin.ext hv)
      have hs := paperAxisPeriodGapSubarc_interiors_disjoint_of_projected_period_injective
        g hg a (hproject a) (properGluingGap g hg a i) (properGluingGap g hg a j) hne
      simpa only [paperAxisProperArc, if_neg hi, if_neg hj] using hs

/-- The actual cyclic successor of a proper-family index, with wrap-around
proved valid from the supplied member of the exact finite index type. -/
def paperAxisProperArcNextIndex (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : paperAxisProperArcIndex g hg a) : paperAxisProperArcIndex g hg a :=
  if hi : i.val + 1 < (paperAxisPeriodCutPoints g hg a).card - 2 then
    ⟨i.val + 1, hi⟩ else ⟨0, by have := i.isLt; omega⟩

private def properGluingCut (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : paperAxisProperArcIndex g hg a) : Fin (paperAxisPeriodCutPoints g hg a).card :=
  ⟨i.val, by have := i.isLt; omega⟩

private def properGluingCutNext (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : paperAxisProperArcIndex g hg a) : Fin (paperAxisPeriodCutPoints g hg a).card :=
  ⟨i.val + 1, by have := i.isLt; omega⟩

private theorem properGluing_parameter_one (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : paperAxisProperArcIndex g hg a) :
    paperAxisProperArcParameter g hg a i 1 =
      paperAxisPeriodCutTable g hg a (properGluingCutNext g hg a i) := by
  by_cases hi : i.val = 0
  · simp only [paperAxisProperArcParameter, if_pos hi,
      show ((1 : unitInterval) : ℝ) = 1 from rfl, mul_one, add_sub_cancel,
      paperAxisWrapRightTime]
    congr 1
    apply Fin.ext
    change 0 + 1 = i.val + 1
    omega
  · simp only [paperAxisProperArcParameter, if_neg hi, paperAxisPeriodGapParameter,
      show ((1 : unitInterval) : ℝ) = 1 from rfl, mul_one, add_sub_cancel]
    rfl

private theorem properGluing_parameter_zero_of_pos (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (i : paperAxisProperArcIndex g hg a) (hi : i.val ≠ 0) :
    paperAxisProperArcParameter g hg a i 0 =
      paperAxisPeriodCutTable g hg a (properGluingCut g hg a i) := by
  simp only [paperAxisProperArcParameter, if_neg hi, paperAxisPeriodGapParameter,
    show ((0 : unitInterval) : ℝ) = 0 from rfl, mul_zero, add_zero]
  rfl

/-- Every actual family target projects to the actual next family source;
the final-to-wrap case uses precisely the actual deck-period action. -/
theorem paperAxisProperArc_projected_gluing (g : modularTraceSubgroup)
    (hg : 2 < |(g.val : IntMatrixTwo).trace|) (a : ℝ)
    (ha : a ∉ paperAxisSideCuts g hg) (i : paperAxisProperArcIndex g hg a) :
    modularTraceQuotientMk (paperAxisProperArc g hg a ha i 1) =
      modularTraceQuotientMk (paperAxisProperArc g hg a ha
        (paperAxisProperArcNextIndex g hg a i) 0) := by
  rw [paperAxisProperArc_project, paperAxisProperArc_project, properGluing_parameter_one]
  by_cases hn : i.val + 1 < (paperAxisPeriodCutPoints g hg a).card - 2
  · have hj : (paperAxisProperArcNextIndex g hg a i).val ≠ 0 := by
      simp only [paperAxisProperArcNextIndex, dif_pos hn]
      omega
    rw [properGluing_parameter_zero_of_pos g hg a _ hj]
    have he : properGluingCutNext g hg a i =
        properGluingCut g hg a (paperAxisProperArcNextIndex g hg a i) := by
      apply Fin.ext
      simp only [paperAxisProperArcNextIndex, dif_pos hn]
      rfl
    rw [he]
  · have hj : (paperAxisProperArcNextIndex g hg a i).val = 0 := by
      simp only [paperAxisProperArcNextIndex, dif_neg hn]
    simp only [paperAxisProperArcParameter, if_pos hj,
      show ((0 : unitInterval) : ℝ) = 0 from rfl, mul_zero, add_zero]
    have he : properGluingCutNext g hg a i =
        paperAxisGapLeftIndex g hg a (paperAxisLastGapIndex g hg a) := by
      apply Fin.ext
      have := i.isLt
      change i.val + 1 = (paperAxisPeriodCutPoints g hg a).card - 2
      omega
    rw [he]
    have ht : paperAxisPeriodCutTable g hg a
        (paperAxisGapLeftIndex g hg a (paperAxisLastGapIndex g hg a)) =
        paperAxisWrapLeftTime g hg a + modularClosedGeodesicPeriod g := by
      dsimp only [paperAxisWrapLeftTime]
      ring
    rw [ht]
    exact modularClosedGeodesic_periodic g hg (paperAxisWrapLeftTime g hg a)

end Markov
