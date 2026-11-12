import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Function.Floor

/-! Mellin transform of the actual bounded fractional part on (1,∞).
This is the analytic remainder in the elementary zeta continuation. -/
noncomputable section
open Filter Set MeasureTheory Asymptotics Complex
open scoped Topology
namespace Markov

def t1_fractionalTail : ℝ → ℂ := (Ioi (1 : ℝ)).indicator fun x => (↑(Int.fract x : ℝ) : ℂ)

theorem t1_fractionalTail_norm_le (x : ℝ) : ‖t1_fractionalTail x‖ ≤ 1 := by
  by_cases hx : x ∈ Ioi (1 : ℝ)
  · rw [t1_fractionalTail,indicator_of_mem hx,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Int.fract_nonneg x)]
    exact (Int.fract_lt_one x).le
  · rw [t1_fractionalTail,indicator_of_notMem hx,norm_zero]
    exact zero_le_one

theorem t1_fractionalTail_measurable : Measurable t1_fractionalTail :=
  ((Complex.continuous_ofReal.measurable.comp measurable_fract :
    Measurable (Complex.ofReal ∘ (Int.fract : ℝ → ℝ)))).indicator measurableSet_Ioi

theorem t1_fractionalTail_locallyIntegrable :
    LocallyIntegrableOn t1_fractionalTail (Ioi (0 : ℝ)) := by
  apply LocallyIntegrable.locallyIntegrableOn
  apply LocallyIntegrable.mono (f := fun _ : ℝ => (1 : ℂ))
    continuous_const.locallyIntegrable t1_fractionalTail_measurable.aestronglyMeasurable
  exact Eventually.of_forall fun x => by simpa only [norm_one] using t1_fractionalTail_norm_le x

theorem t1_fractionalTail_atTop :
    t1_fractionalTail =O[atTop] (fun x : ℝ => x^(-(0 : ℝ))) := by
  apply IsBigO.of_bound 1
  exact Eventually.of_forall fun x => by simpa using t1_fractionalTail_norm_le x

theorem t1_fractionalTail_atZero (b : ℝ) :
    t1_fractionalTail =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x^(-b)) := by
  apply IsBigO.of_bound 1
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ)<1 by norm_num))]
    with x hx
  have hx' : x ∉ Ioi (1 : ℝ) := by simp only [mem_Ioi,not_lt]; exact hx.le
  rw [t1_fractionalTail,indicator_of_notMem hx',norm_zero,one_mul]
  exact norm_nonneg _

def t1_zetaFractionalMellin (s : ℂ) : ℂ := mellin t1_fractionalTail (-s)

theorem t1_zetaFractionalMellin_differentiableAt {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ t1_zetaFractionalMellin s := by
  have h := mellin_differentiableAt_of_isBigO_rpow t1_fractionalTail_locallyIntegrable
    t1_fractionalTail_atTop (show (-s).re < 0 by simpa only [neg_re,neg_neg,neg_lt_zero])
    (t1_fractionalTail_atZero (-s.re-1)) (show -s.re-1 < (-s).re by simp only [neg_re]; linarith)
  exact h.comp s differentiableAt_id.neg

theorem t1_zetaFractionalMellin_integral (s : ℂ) :
    t1_zetaFractionalMellin s =
      ∫ x : ℝ in Ioi (1 : ℝ), (↑(Int.fract x : ℝ) : ℂ)*(x : ℂ)^(-(s+1)) := by
  rw [t1_zetaFractionalMellin,mellin]
  have hpoint (x : ℝ) :
      (x : ℂ)^(-s-1) • t1_fractionalTail x =
        (Ioi (1 : ℝ)).indicator (fun x : ℝ => (↑(Int.fract x : ℝ) : ℂ)*(x : ℂ)^(-(s+1))) x := by
    by_cases hx : x ∈ Ioi (1 : ℝ)
    · rw [t1_fractionalTail,indicator_of_mem hx,indicator_of_mem hx,smul_eq_mul,
        show -s-1 = -(s+1) by ring,mul_comm]
    · rw [t1_fractionalTail,indicator_of_notMem hx,indicator_of_notMem hx,smul_zero]
  simp_rw [hpoint,integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi (show (0 : ℝ)≤1 by norm_num))]

end Markov
