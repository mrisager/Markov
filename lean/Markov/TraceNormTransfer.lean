import Markov.PrimitiveNormUniqueness
import Markov.TraceLatticeAsymptotic

/-! Transfer of the lattice estimate under primitive-length agreement.
The geometric instance is in `IntrinsicMcShaneRivinCount`. -/

noncomputable section
open Set MeasureTheory Filter Asymptotics
open scoped Pointwise Topology
namespace Markov

/-- A continuous homogeneous plane function agreeing with the constructed
trace norm on all primitive vectors is that norm everywhere. -/
theorem eq_traceEuclideanGauge_of_primitive_values
    (F : EuclideanSpace ℝ (Fin 2) → ℝ) (hF : Continuous F)
    (hhom : ∀ a : ℝ, ∀ x, F (a • x) = |a| * F x)
    (hp : ∀ d : ℤ × ℤ, IsCoprime d.1 d.2 →
      F (euclideanIntDirection d) = ‖intVector traceBasis d‖) :
    F = traceEuclideanGauge := by
  apply continuous_homogeneous_euclidean_ext_of_primitive F traceEuclideanGauge hF
    (continuous_norm.comp traceEuclideanEquiv.symm.continuous) hhom traceEuclideanGauge_smul
  intro d hd
  rw [hp d hd, traceEuclideanGauge_intDirection]

theorem unitSublevel_eq_traceEuclideanBall_of_primitive_values
    (F : EuclideanSpace ℝ (Fin 2) → ℝ) (hF : Continuous F)
    (hhom : ∀ a : ℝ, ∀ x, F (a • x) = |a| * F x)
    (hp : ∀ d : ℤ × ℤ, IsCoprime d.1 d.2 →
      F (euclideanIntDirection d) = ‖intVector traceBasis d‖) :
    {x | F x ≤ 1} = traceEuclideanBall := by
  rw [eq_traceEuclideanGauge_of_primitive_values F hF hhom hp]
  ext x
  exact (mem_traceEuclideanBall_iff x).symm

/-- The full lattice count and Euclidean area transfer under the displayed
primitive-value agreement hypothesis. -/
theorem lattice_asymptotic_of_primitive_values
    (F : EuclideanSpace ℝ (Fin 2) → ℝ) (hF : Continuous F)
    (hhom : ∀ a : ℝ, ∀ x, F (a • x) = |a| * F x)
    (hp : ∀ d : ℤ × ℤ, IsCoprime d.1 d.2 →
      F (euclideanIntDirection d) = ‖intVector traceBasis d‖) :
    (fun R : ℝ =>
      (({d : ℤ × ℤ | euclideanIntDirection d ∈ R • {x | F x ≤ 1}}).ncard : ℝ) -
        (volume {x | F x ≤ 1}).toReal * R ^ 2) =O[atTop]
      (fun R : ℝ => R / Real.log R ^ (3 / 2 : ℝ)) := by
  rw [unitSublevel_eq_traceEuclideanBall_of_primitive_values F hF hhom hp]
  apply trace_lattice_asymptotic.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [traceLatticeCount_eq_ncard_actual R hR]
  rfl

end Markov
