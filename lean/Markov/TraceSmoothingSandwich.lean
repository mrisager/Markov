import Markov.TraceRadialMollifier
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! The actual mollifier sandwich for the constructed trace ball, in the
fixed Euclidean coordinates and with the full integer lattice. -/

noncomputable section
open Set MeasureTheory Function
open scoped Pointwise Convolution Topology ContDiff
namespace Markov

theorem isCompact_smul_traceEuclideanBall (R : ℝ) :
    IsCompact (R • traceEuclideanBall) :=
  isCompact_traceEuclideanBall.image (continuous_const.smul continuous_id)

theorem measurableSet_smul_traceEuclideanBall (R : ℝ) :
    MeasurableSet (R • traceEuclideanBall) :=
  (isCompact_smul_traceEuclideanBall R).measurableSet

/-- The indicator of an actual dilate of the constructed trace unit ball. -/
def traceBallIndicator (R : ℝ) : EuclideanSpace ℝ (Fin 2) → ℝ :=
  (R • traceEuclideanBall).indicator (fun _ => 1)

theorem traceBallIndicator_nonneg (R : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    0 ≤ traceBallIndicator R x := by
  classical
  by_cases hx : x ∈ R • traceEuclideanBall <;> simp [traceBallIndicator, hx]

theorem traceBallIndicator_le_one (R : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    traceBallIndicator R x ≤ 1 := by
  classical
  by_cases hx : x ∈ R • traceEuclideanBall <;> simp [traceBallIndicator, hx]

theorem traceBallIndicator_integrable (R : ℝ) : Integrable (traceBallIndicator R) := by
  apply (integrable_indicator_iff (measurableSet_smul_traceEuclideanBall R)).mpr
  exact integrableOn_const (isCompact_smul_traceEuclideanBall R).measure_ne_top

theorem traceBallIndicator_hasCompactSupport (R : ℝ) :
    HasCompactSupport (traceBallIndicator R) := by
  apply HasCompactSupport.intro (isCompact_smul_traceEuclideanBall R)
  intro x hx
  exact indicator_of_notMem hx (fun _ => (1 : ℝ))

/-- The actual smoothing, with the unit-mass radial kernel on the left. -/
def traceSmoothedIndicator (R Q : ℝ) : EuclideanSpace ℝ (Fin 2) → ℝ :=
  traceScaledMollifier Q ⋆ traceBallIndicator R

theorem traceSmoothedIndicator_apply (R Q : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    traceSmoothedIndicator R Q x =
      ∫ y, traceScaledMollifier Q y * traceBallIndicator R (x - y) := rfl

theorem traceSmoothedIndicator_integrand_integrable (R Q : ℝ) (hQ : 0 < Q)
    (x : EuclideanSpace ℝ (Fin 2)) :
    Integrable (fun y => traceScaledMollifier Q y * traceBallIndicator R (x - y)) := by
  have hs : MeasurableSet ((fun y : EuclideanSpace ℝ (Fin 2) => x - y) ⁻¹'
      (R • traceEuclideanBall)) :=
    (measurableSet_smul_traceEuclideanBall R).preimage (measurable_const.sub measurable_id)
  have hi := (traceScaledMollifier_integrable Q hQ).indicator hs
  convert hi using 1
  ext y
  classical
  by_cases hy : x - y ∈ R • traceEuclideanBall <;>
    simp [traceBallIndicator, hy]

theorem traceSmoothedIndicator_nonneg (R Q : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    0 ≤ traceSmoothedIndicator R Q x :=
  integral_nonneg (fun y => mul_nonneg (traceScaledMollifier_nonneg Q y)
    (traceBallIndicator_nonneg R (x - y)))

theorem traceSmoothedIndicator_le_one (R Q : ℝ) (hQ : 0 < Q)
    (x : EuclideanSpace ℝ (Fin 2)) : traceSmoothedIndicator R Q x ≤ 1 := by
  rw [traceSmoothedIndicator_apply, ← traceScaledMollifier_integral Q hQ]
  apply integral_mono (traceSmoothedIndicator_integrand_integrable R Q hQ x)
    (traceScaledMollifier_integrable Q hQ)
  intro y
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (traceBallIndicator_le_one R (x - y)) (traceScaledMollifier_nonneg Q y)

theorem traceSmoothedIndicator_integrable (R Q : ℝ) (hQ : 0 < Q) :
    Integrable (traceSmoothedIndicator R Q) :=
  (traceScaledMollifier_integrable Q hQ).integrable_convolution
    (ContinuousLinearMap.lsmul ℝ ℝ) (traceBallIndicator_integrable R)

theorem traceSmoothedIndicator_hasCompactSupport (R Q : ℝ) (hQ : 0 < Q) :
    HasCompactSupport (traceSmoothedIndicator R Q) :=
  (traceScaledMollifier_hasCompactSupport Q hQ).convolution
    (ContinuousLinearMap.lsmul ℝ ℝ) (traceBallIndicator_hasCompactSupport R)

theorem traceSmoothedIndicator_contDiff (R Q : ℝ) (hQ : 0 < Q) :
    ContDiff ℝ ∞ (traceSmoothedIndicator R Q) :=
  (traceScaledMollifier_hasCompactSupport Q hQ).contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (traceScaledMollifier_contDiff Q)
    (traceBallIndicator_integrable R).locallyIntegrable

theorem traceEuclideanGauge_sub_le (x y : EuclideanSpace ℝ (Fin 2)) :
    traceEuclideanGauge (x - y) ≤ traceEuclideanGauge x + traceEuclideanGauge y := by
  simp only [traceEuclideanGauge, map_sub]
  exact norm_sub_le _ _

/-- The gauge displacement of every point where the smoothing kernel is nonzero. -/
theorem traceScaledMollifier_gauge_le (Q : ℝ) (hQ : 0 < Q)
    (y : EuclideanSpace ℝ (Fin 2)) (hy : traceScaledMollifier Q y ≠ 0) :
    traceEuclideanGauge y ≤ traceEuclideanGaugeConstant / Q := by
  have hy' : y ∈ support (traceScaledMollifier Q) := hy
  rw [traceScaledMollifier_support_eq Q hQ] at hy'
  have hnlt : ‖y‖ < Q⁻¹ := by simpa only [Metric.mem_ball, dist_zero_right] using hy'
  have hn : ‖y‖ ≤ Q⁻¹ := hnlt.le
  exact (traceEuclideanGauge_le y).trans
    (by simpa only [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left hn traceEuclideanGaugeConstant_pos.le)

theorem traceSmoothedIndicator_eq_zero_of_gauge_lt (S Q : ℝ) (hS : 0 < S)
    (hQ : 0 < Q) (x : EuclideanSpace ℝ (Fin 2))
    (hx : S + traceEuclideanGaugeConstant / Q < traceEuclideanGauge x) :
    traceSmoothedIndicator S Q x = 0 := by
  rw [traceSmoothedIndicator_apply]
  apply integral_eq_zero_of_ae
  apply Filter.Eventually.of_forall
  intro y
  change traceScaledMollifier Q y * traceBallIndicator S (x - y) = 0
  classical
  by_cases hy : traceScaledMollifier Q y = 0
  · rw [hy, zero_mul]
  · have hnot : x - y ∉ S • traceEuclideanBall := by
      intro hm
      have hm' := (mem_smul_traceEuclideanBall_iff S hS (x - y)).mp hm
      have hg := traceEuclideanGauge_add_le (x - y) y
      rw [sub_add_cancel] at hg
      have hy' := traceScaledMollifier_gauge_le Q hQ y hy
      linarith
    simp only [traceBallIndicator, indicator_of_notMem hnot, mul_zero]

theorem traceSmoothedIndicator_eq_one_of_gauge_le (S Q : ℝ) (hS : 0 < S)
    (hQ : 0 < Q) (x : EuclideanSpace ℝ (Fin 2))
    (hx : traceEuclideanGauge x + traceEuclideanGaugeConstant / Q ≤ S) :
    traceSmoothedIndicator S Q x = 1 := by
  rw [traceSmoothedIndicator_apply, ← traceScaledMollifier_integral Q hQ]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  change traceScaledMollifier Q y * traceBallIndicator S (x - y) = traceScaledMollifier Q y
  classical
  by_cases hy : traceScaledMollifier Q y = 0
  · rw [hy, zero_mul]
  · have hm : x - y ∈ S • traceEuclideanBall := by
      apply (mem_smul_traceEuclideanBall_iff S hS (x - y)).mpr
      have hg := traceEuclideanGauge_sub_le x y
      have hy' := traceScaledMollifier_gauge_le Q hQ y hy
      linarith
    simp only [traceBallIndicator, indicator_of_mem hm, mul_one]

/-- Smoothing the inner and outer actual balls sandwiches the actual indicator.
The displacement is `c/Q`, where `c` is the proved Euclidean gauge bound. -/
theorem traceSmoothingSandwich (R Q : ℝ) (hQ : 0 < Q)
    (hR : 0 < R - traceEuclideanGaugeConstant / Q)
    (x : EuclideanSpace ℝ (Fin 2)) :
    traceSmoothedIndicator (R - traceEuclideanGaugeConstant / Q) Q x ≤
        traceBallIndicator R x ∧
      traceBallIndicator R x ≤
        traceSmoothedIndicator (R + traceEuclideanGaugeConstant / Q) Q x := by
  have he : 0 < traceEuclideanGaugeConstant / Q :=
    div_pos traceEuclideanGaugeConstant_pos hQ
  have hRp : 0 < R := by linarith
  have hplus : 0 < R + traceEuclideanGaugeConstant / Q := by linarith
  classical
  by_cases hx : x ∈ R • traceEuclideanBall
  · have hg := (mem_smul_traceEuclideanBall_iff R hRp x).mp hx
    rw [show traceBallIndicator R x = 1 from indicator_of_mem hx (fun _ => (1 : ℝ))]
    constructor
    · exact traceSmoothedIndicator_le_one _ Q hQ x
    · rw [traceSmoothedIndicator_eq_one_of_gauge_le _ Q hplus hQ x (by linarith)]
  · have hg : R < traceEuclideanGauge x :=
      lt_of_not_ge (fun hh => hx ((mem_smul_traceEuclideanBall_iff R hRp x).mpr hh))
    rw [show traceBallIndicator R x = 0 from indicator_of_notMem hx (fun _ => (1 : ℝ))]
    constructor
    · rw [traceSmoothedIndicator_eq_zero_of_gauge_lt _ Q hR hQ x (by linarith)]
    · exact traceSmoothedIndicator_nonneg _ Q x

/-- The same pointwise sandwich may be summed over any finite set of full
integer lattice points. -/
theorem traceSmoothingSandwich_finset (N : Finset (ℤ × ℤ)) (R Q : ℝ) (hQ : 0 < Q)
    (hR : 0 < R - traceEuclideanGaugeConstant / Q) :
    (∑ n ∈ N, traceSmoothedIndicator (R - traceEuclideanGaugeConstant / Q) Q
        (euclideanIntDirection n)) ≤
        ∑ n ∈ N, traceBallIndicator R (euclideanIntDirection n) ∧
      (∑ n ∈ N, traceBallIndicator R (euclideanIntDirection n)) ≤
        ∑ n ∈ N, traceSmoothedIndicator (R + traceEuclideanGaugeConstant / Q) Q
          (euclideanIntDirection n) := by
  constructor
  · exact Finset.sum_le_sum (fun n _ => (traceSmoothingSandwich R Q hQ hR _).1)
  · exact Finset.sum_le_sum (fun n _ => (traceSmoothingSandwich R Q hQ hR _).2)

theorem traceBallIndicator_intDirection (R : ℝ) (hR : 0 < R) (n : ℤ × ℤ) :
    traceBallIndicator R (euclideanIntDirection n) =
      if n ∈ traceLatticePoints R then 1 else 0 := by
  classical
  simp only [traceBallIndicator, Set.indicator_apply,
    mem_smul_traceEuclideanBall_iff R hR, traceEuclideanGauge_intDirection,
    mem_traceLatticePoints]

theorem sum_traceBallIndicator_eq_count (N : Finset (ℤ × ℤ)) (R : ℝ) (hR : 0 < R)
    (hN : traceLatticePoints R ⊆ N) :
    ∑ n ∈ N, traceBallIndicator R (euclideanIntDirection n) = (traceLatticeCount R : ℝ) := by
  classical
  calc
    _ = ∑ n ∈ traceLatticePoints R, traceBallIndicator R (euclideanIntDirection n) := by
      symm
      apply Finset.sum_subset hN
      intro n _ hn
      rw [traceBallIndicator_intDirection R hR n, if_neg hn]
    _ = ∑ _n ∈ traceLatticePoints R, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [traceBallIndicator_intDirection R hR n, if_pos hn]
    _ = _ := by simp [traceLatticeCount]

theorem traceLatticePoints_mono (a b : ℝ) (hab : a ≤ b) :
    traceLatticePoints a ⊆ traceLatticePoints b := by
  intro n hn
  exact (mem_traceLatticePoints b n).mpr (((mem_traceLatticePoints a n).mp hn).trans hab)

theorem traceSmoothedIndicator_intDirection_eq_zero (S Q : ℝ) (hS : 0 < S) (hQ : 0 < Q)
    (n : ℤ × ℤ) (hn : n ∉ traceLatticePoints (S + traceEuclideanGaugeConstant / Q)) :
    traceSmoothedIndicator S Q (euclideanIntDirection n) = 0 := by
  apply traceSmoothedIndicator_eq_zero_of_gauge_lt S Q hS hQ
  rw [traceEuclideanGauge_intDirection]
  exact lt_of_not_ge (fun hh => hn ((mem_traceLatticePoints _ n).mpr hh))

/-- The full lattice sum of the smoothing, represented by its proved finite
support window. This is a sum over all integer pairs, with no primitive filter. -/
def traceSmoothedLatticeCount (S Q : ℝ) : ℝ :=
  ∑ n ∈ traceLatticePoints (S + traceEuclideanGaugeConstant / Q),
    traceSmoothedIndicator S Q (euclideanIntDirection n)

theorem traceSmoothedLatticeCount_hasSum (S Q : ℝ) (hS : 0 < S) (hQ : 0 < Q) :
    HasSum (fun n : ℤ × ℤ => traceSmoothedIndicator S Q (euclideanIntDirection n))
      (traceSmoothedLatticeCount S Q) :=
  hasSum_sum_of_ne_finset_zero (fun n hn =>
    traceSmoothedIndicator_intDirection_eq_zero S Q hS hQ n hn)

theorem traceSmoothedLatticeCount_eq_tsum (S Q : ℝ) (hS : 0 < S) (hQ : 0 < Q) :
    traceSmoothedLatticeCount S Q =
      ∑' n : ℤ × ℤ, traceSmoothedIndicator S Q (euclideanIntDirection n) :=
  (traceSmoothedLatticeCount_hasSum S Q hS hQ).tsum_eq.symm

theorem traceSmoothedLatticeCount_eq_sum (N : Finset (ℤ × ℤ)) (S Q : ℝ)
    (hS : 0 < S) (hQ : 0 < Q)
    (hN : traceLatticePoints (S + traceEuclideanGaugeConstant / Q) ⊆ N) :
    traceSmoothedLatticeCount S Q =
      ∑ n ∈ N, traceSmoothedIndicator S Q (euclideanIntDirection n) := by
  apply Finset.sum_subset hN
  intro n _ hn
  exact traceSmoothedIndicator_intDirection_eq_zero S Q hS hQ n hn

/-- The exact full lattice count is between the inner and outer smoothed
lattice sums. Each smoothed sum is finite by the proved gauge support bound. -/
theorem traceSmoothingSandwich_latticeCount (R Q : ℝ) (hQ : 0 < Q)
    (hR : 0 < R - traceEuclideanGaugeConstant / Q) :
    traceSmoothedLatticeCount (R - traceEuclideanGaugeConstant / Q) Q ≤
        (traceLatticeCount R : ℝ) ∧
      (traceLatticeCount R : ℝ) ≤
        traceSmoothedLatticeCount (R + traceEuclideanGaugeConstant / Q) Q := by
  have he : 0 < traceEuclideanGaugeConstant / Q :=
    div_pos traceEuclideanGaugeConstant_pos hQ
  have hRp : 0 < R := by linarith
  have hplus : 0 < R + traceEuclideanGaugeConstant / Q := by linarith
  let N := traceLatticePoints (R + 2 * (traceEuclideanGaugeConstant / Q))
  have hNinner : traceLatticePoints (R - traceEuclideanGaugeConstant / Q +
      traceEuclideanGaugeConstant / Q) ⊆ N :=
    traceLatticePoints_mono _ _ (by linarith)
  have hNouter : traceLatticePoints (R + traceEuclideanGaugeConstant / Q +
      traceEuclideanGaugeConstant / Q) ⊆ N :=
    traceLatticePoints_mono _ _ (by linarith)
  have hN : traceLatticePoints R ⊆ N := traceLatticePoints_mono _ _ (by linarith)
  rw [traceSmoothedLatticeCount_eq_sum N _ Q hR hQ hNinner,
    traceSmoothedLatticeCount_eq_sum N _ Q hplus hQ hNouter,
    ← sum_traceBallIndicator_eq_count N R hRp hN]
  exact traceSmoothingSandwich_finset N R Q hQ hR

end Markov
