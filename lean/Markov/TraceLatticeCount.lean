import Markov.TraceEuclideanSupport
import Markov.NormalDeterminant
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! Exact counting of the full integer lattice in the constructed trace ball.
The Euclidean coordinates are the fixed basis coordinates, so all pairs in
`ℤ × ℤ`, including zero and nonprimitive pairs, are counted. -/

noncomputable section
open Set MeasureTheory
open scoped Pointwise ENNReal
namespace Markov

/-- The original trace norm, evaluated in the fixed Euclidean coordinates. -/
def traceEuclideanGauge (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ‖traceEuclideanEquiv.symm x‖

@[simp] theorem traceEuclideanGauge_coordinates (x : TracePlane) :
    traceEuclideanGauge (traceEuclideanCoordinates x) = ‖x‖ := by
  change ‖traceEuclideanEquiv.symm (traceEuclideanEquiv x)‖ = ‖x‖
  simp

@[simp] theorem traceEuclideanGauge_zero : traceEuclideanGauge 0 = 0 := by
  simp [traceEuclideanGauge]

theorem traceEuclideanGauge_nonneg (x : EuclideanSpace ℝ (Fin 2)) :
    0 ≤ traceEuclideanGauge x := norm_nonneg _

theorem traceEuclideanGauge_add_le (x y : EuclideanSpace ℝ (Fin 2)) :
    traceEuclideanGauge (x + y) ≤ traceEuclideanGauge x + traceEuclideanGauge y := by
  simp only [traceEuclideanGauge, map_add]
  exact norm_add_le _ _

theorem traceEuclideanGauge_smul (r : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    traceEuclideanGauge (r • x) = |r| * traceEuclideanGauge x := by
  simp [traceEuclideanGauge, norm_smul, Real.norm_eq_abs]

theorem mem_traceEuclideanBall_iff (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ traceEuclideanBall ↔ traceEuclideanGauge x ≤ 1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [traceEuclideanGauge_coordinates, Metric.mem_closedBall,
      dist_zero_right] using hy
  · intro hx
    refine ⟨traceEuclideanEquiv.symm x, ?_, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    · change traceEuclideanEquiv (traceEuclideanEquiv.symm x) = x
      simp

theorem mem_smul_traceEuclideanBall_iff (R : ℝ) (hR : 0 < R)
    (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ R • traceEuclideanBall ↔ traceEuclideanGauge x ≤ R := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [traceEuclideanGauge_smul, abs_of_pos hR]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left ((mem_traceEuclideanBall_iff y).mp hy) hR.le
  · intro hx
    refine ⟨R⁻¹ • x, (mem_traceEuclideanBall_iff _).mpr ?_, ?_⟩
    · rw [traceEuclideanGauge_smul, abs_of_pos (inv_pos.mpr hR)]
      calc
        R⁻¹ * traceEuclideanGauge x ≤ R⁻¹ * R :=
          mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hR.le)
        _ = 1 := inv_mul_cancel₀ hR.ne'
    · simp only [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]

/-- The original integer vector has exactly the standard integer coordinates. -/
@[simp] theorem traceEuclideanCoordinates_intVector (n : ℤ × ℤ) :
    traceEuclideanCoordinates (intVector traceBasis n) = euclideanIntDirection n := by
  rw [intVector, map_add, map_smul, map_smul,
    traceEuclideanCoordinates_basis, traceEuclideanCoordinates_basis]
  ext i
  fin_cases i <;> simp [euclideanIntDirection, EuclideanSpace.single_apply]

@[simp] theorem traceEuclideanGauge_intDirection (n : ℤ × ℤ) :
    traceEuclideanGauge (euclideanIntDirection n) = ‖intVector traceBasis n‖ := by
  rw [← traceEuclideanCoordinates_intVector, traceEuclideanGauge_coordinates]

/-- A positive Lipschitz bound for the gauge in the Euclidean norm. -/
def traceEuclideanGaugeConstant : ℝ := ‖traceEuclideanEquiv.symm.toContinuousLinearMap‖ + 1

theorem traceEuclideanGaugeConstant_pos : 0 < traceEuclideanGaugeConstant := by
  unfold traceEuclideanGaugeConstant
  positivity

theorem traceEuclideanGauge_le (x : EuclideanSpace ℝ (Fin 2)) :
    traceEuclideanGauge x ≤ traceEuclideanGaugeConstant * ‖x‖ := by
  exact (traceEuclideanEquiv.symm.toContinuousLinearMap.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (by simp [traceEuclideanGaugeConstant]) (norm_nonneg x))

/-- A concrete positive Euclidean inradius of the actual trace ball. -/
def traceEuclideanInradius : ℝ := traceEuclideanGaugeConstant⁻¹

theorem traceEuclideanInradius_pos : 0 < traceEuclideanInradius :=
  inv_pos.mpr traceEuclideanGaugeConstant_pos

theorem closedBall_subset_traceEuclideanBall :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) traceEuclideanInradius ⊆
      traceEuclideanBall := by
  intro x hx
  apply (mem_traceEuclideanBall_iff x).mpr
  have hx' : ‖x‖ ≤ traceEuclideanGaugeConstant⁻¹ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, traceEuclideanInradius] using hx
  exact (traceEuclideanGauge_le x).trans
    ((mul_le_mul_of_nonneg_left hx' traceEuclideanGaugeConstant_pos.le).trans_eq
      (mul_inv_cancel₀ traceEuclideanGaugeConstant_pos.ne'))

/-- An explicit finite box containing every integer point of trace radius `R`. -/
def traceLatticeCoordinateBound (R : ℝ) : ℤ :=
  ⌈‖traceEuclideanCoordinates‖ * max R 0⌉

def traceLatticeCoordinateBox (R : ℝ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-traceLatticeCoordinateBound R) (traceLatticeCoordinateBound R)).product
    (Finset.Icc (-traceLatticeCoordinateBound R) (traceLatticeCoordinateBound R))

theorem intVector_mem_traceLatticeCoordinateBox (R : ℝ) (n : ℤ × ℤ)
    (hn : ‖intVector traceBasis n‖ ≤ R) : n ∈ traceLatticeCoordinateBox R := by
  have hb : ‖euclideanIntDirection n‖ ≤ ‖traceEuclideanCoordinates‖ * max R 0 := by
    rw [← traceEuclideanCoordinates_intVector]
    exact (traceEuclideanCoordinates.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hn.trans (le_max_left R 0)) (norm_nonneg _))
  have hc (i : Fin 2) : |euclideanIntDirection n i| ≤
      (traceLatticeCoordinateBound R : ℝ) := by
    have hi : |euclideanIntDirection n i| ≤ ‖euclideanIntDirection n‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (euclideanIntDirection n) i
    exact hi.trans (hb.trans (Int.le_ceil _))
  have h0 : |(n.1 : ℝ)| ≤ (traceLatticeCoordinateBound R : ℝ) := by
    simpa [euclideanIntDirection] using hc 0
  have h1 : |(n.2 : ℝ)| ≤ (traceLatticeCoordinateBound R : ℝ) := by
    simpa [euclideanIntDirection] using hc 1
  have h0' : -traceLatticeCoordinateBound R ≤ n.1 ∧ n.1 ≤ traceLatticeCoordinateBound R := by
    exact_mod_cast abs_le.mp h0
  have h1' : -traceLatticeCoordinateBound R ≤ n.2 ∧ n.2 ≤ traceLatticeCoordinateBound R := by
    exact_mod_cast abs_le.mp h1
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr h0', Finset.mem_Icc.mpr h1'⟩

/-- The exact full lattice-point finset; no primitivity or nonzero filter is imposed. -/
def traceLatticePoints (R : ℝ) : Finset (ℤ × ℤ) := by
  classical
  exact (traceLatticeCoordinateBox R).filter (fun n => ‖intVector traceBasis n‖ ≤ R)

@[simp] theorem mem_traceLatticePoints (R : ℝ) (n : ℤ × ℤ) :
    n ∈ traceLatticePoints R ↔ ‖intVector traceBasis n‖ ≤ R := by
  classical
  simp only [traceLatticePoints, Finset.mem_filter]
  exact ⟨And.right, fun hn => ⟨intVector_mem_traceLatticeCoordinateBox R n hn, hn⟩⟩

/-- The actual integer preimage of the Euclidean dilate of the trace unit ball. -/
def traceEuclideanLatticeSet (R : ℝ) : Set (ℤ × ℤ) :=
  {n | euclideanIntDirection n ∈ R • traceEuclideanBall}

theorem traceLatticePoints_eq_actual (R : ℝ) (hR : 0 < R) :
    (traceLatticePoints R : Set (ℤ × ℤ)) = traceEuclideanLatticeSet R := by
  ext n
  simp only [Finset.mem_coe, mem_traceLatticePoints, traceEuclideanLatticeSet,
    Set.mem_setOf_eq, mem_smul_traceEuclideanBall_iff R hR, traceEuclideanGauge_intDirection]

theorem traceEuclideanLatticeSet_finite (R : ℝ) (hR : 0 < R) :
    (traceEuclideanLatticeSet R).Finite := by
  rw [← traceLatticePoints_eq_actual R hR]
  exact Finset.finite_toSet _

/-- The exact number of all integer lattice points in trace radius `R`. -/
def traceLatticeCount (R : ℝ) : ℕ := (traceLatticePoints R).card

theorem traceLatticeCount_eq_ncard_actual (R : ℝ) (hR : 0 < R) :
    traceLatticeCount R = (traceEuclideanLatticeSet R).ncard := by
  rw [← traceLatticePoints_eq_actual R hR]
  simp only [traceLatticeCount, Set.ncard_coe_finset]

/-- Euclidean area in the fixed homology coordinates, with standard volume. -/
def traceEuclideanArea : ℝ := (volume traceEuclideanBall).toReal

theorem traceEuclideanBall_volume_lt_top : volume traceEuclideanBall < ∞ :=
  isCompact_traceEuclideanBall.measure_lt_top

theorem traceEuclideanBall_volume_pos : 0 < volume traceEuclideanBall :=
  (Metric.measure_closedBall_pos volume _ traceEuclideanInradius_pos).trans_le
    (measure_mono closedBall_subset_traceEuclideanBall)

theorem traceEuclideanArea_pos : 0 < traceEuclideanArea := by
  exact ENNReal.toReal_pos traceEuclideanBall_volume_pos.ne'
    traceEuclideanBall_volume_lt_top.ne

end Markov
