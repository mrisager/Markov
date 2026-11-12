import Markov.PrimitiveSimpleGeodesicExistence

/-! A geometric length set defined using all actual embedded locally unit-speed
geodesic circles with the prescribed genuine H1 class. The definition contains
no trace words or trace-norm values. Only nonemptiness and an upper bound are
proved here. No arbitrary simple-class classification, norm or B_X is asserted. -/

noncomputable section
open Set Topology
namespace Markov

/-- The actual positive once-around path of a metric-period circle map. -/
def modularMetricCirclePositiveLoop (L : ℝ)
    (q : C(AddCircle L, ModularTraceQuotient)) : Path (q 0) (q 0) :=
  (((Path.segment (0 : ℝ) L).map (AddCircle.continuous_mk' L)).cast
    rfl (AddCircle.coe_period L).symm).map q.continuous

@[simp] theorem modularMetricCirclePositiveLoop_apply (L : ℝ)
    (q : C(AddCircle L, ModularTraceQuotient)) (t : unitInterval) :
    modularMetricCirclePositiveLoop L q t = q (((t : ℝ) * L : ℝ) : AddCircle L) := by
  simp [modularMetricCirclePositiveLoop, Path.segment_apply, AffineMap.lineMap_apply_module]

/-- All genuine metric periods of actual oriented simple geodesics with actual
fixed-marking singular H1 p. Closed embedding and unit speed are actual metric
and topological properties, not a classification or a length-agreement field. -/
def modularSimpleGeodesicLengthSet (p : ℤ × ℤ) : Set ℝ :=
  {L | 0 < L ∧ ∃ q : C(AddCircle L, ModularTraceQuotient),
    IsClosedEmbedding q ∧
    LipschitzWith 1 (fun t : ℝ => q (t : AddCircle L)) ∧
    (∀ t : ℝ, ∃ r > 0, ∀ s ∈ Metric.ball t r, ∀ u ∈ Metric.ball t r,
      dist (q (s : AddCircle L)) (q (u : AddCircle L)) = dist s u) ∧
    modularTraceFixedSingularH1Equiv
      (singularLoopClass ModularTraceQuotient (modularMetricCirclePositiveLoop L q)) = p}

/-- Each displayed metric period is its actual one-period metric variation.
This conclusion is derived from the actual unit-speed curve properties. -/
theorem modularSimpleGeodesicLengthSet_metric_variation (p : ℤ × ℤ) (L : ℝ)
    (hL : L ∈ modularSimpleGeodesicLengthSet p) :
    ∃ q : C(AddCircle L, ModularTraceQuotient), IsClosedEmbedding q ∧
      modularTraceFixedSingularH1Equiv
        (singularLoopClass ModularTraceQuotient (modularMetricCirclePositiveLoop L q)) = p ∧
      (eVariationOn (fun t : ℝ => q (t : AddCircle L)) (Icc 0 L)).toReal = L := by
  rcases hL with ⟨hpos, q, hemb, hlip, hlocal, hclass⟩
  refine ⟨q, hemb, hclass, ?_⟩
  have hv := variation_eq_sub_of_local_unit_speed
    (fun t : ℝ => q (t : AddCircle L)) hlip hlocal 0 L
  rw [variationOnFromTo.eq_of_le _ univ hpos.le, univ_inter, sub_zero] at hv
  exact hv

/-- The actual canonical simple geodesic is a member of the independently
defined geometric set. Arbitrary simple geodesics are still allowed in that set. -/
theorem trace_norm_mem_modularSimpleGeodesicLengthSet (p : ℤ × ℤ)
    (hp : IsCoprime p.1 p.2) :
    ‖intVector traceBasis p‖ ∈ modularSimpleGeodesicLengthSet p := by
  obtain ⟨k, hkp, hemb, _, _, hlocal, _, hclass, hperiod, _⟩ :=
    primitive_signedClass_has_canonical_simpleGeodesicCircle p hp
  rw [← hperiod]
  refine ⟨modularClosedGeodesicPeriod_pos (paperPrimitiveHolonomy k p hkp)
    (paperPrimitiveHolonomy_hyperbolic k p hkp),
    paperPrimitiveSimpleGeodesicCircle k p hkp, hemb, ?_, hlocal, ?_⟩
  · simpa only [paperPrimitiveSimpleGeodesicCircle_coe] using
      modularClosedGeodesic_lipschitz (paperPrimitiveHolonomy k p hkp)
        (paperPrimitiveHolonomy_hyperbolic k p hkp)
  · have heq : modularMetricCirclePositiveLoop
        (modularClosedGeodesicPeriod (paperPrimitiveHolonomy k p hkp))
        (paperPrimitiveSimpleGeodesicCircle k p hkp) =
        paperPrimitiveSimpleGeodesicCircleLoop k p hkp := by
      rfl
    rw [heq]
    exact hclass

/-- Primitive actual geometric length sets are genuinely nonempty. -/
theorem modularSimpleGeodesicLengthSet_nonempty (p : ℤ × ℤ)
    (hp : IsCoprime p.1 p.2) : (modularSimpleGeodesicLengthSet p).Nonempty :=
  ⟨_, trace_norm_mem_modularSimpleGeodesicLengthSet p hp⟩

/-- The positive actual metric periods give a concrete lower bound. -/
theorem modularSimpleGeodesicLengthSet_bddBelow (p : ℤ × ℤ) :
    BddBelow (modularSimpleGeodesicLengthSet p) :=
  ⟨0, fun _ hL => hL.1.le⟩

/-- An intrinsic infimum over all actual simple geodesics with the indicated
original class. Its equality to the canonical value, attainment/uniqueness and
norm properties are not asserted. In particular this does not define B_X. -/
def modularSimpleGeodesicLengthInf (p : ℤ × ℤ) : ℝ :=
  sInf (modularSimpleGeodesicLengthSet p)

theorem modularSimpleGeodesicLengthInf_nonneg (p : ℤ × ℤ)
    (hp : IsCoprime p.1 p.2) : 0 ≤ modularSimpleGeodesicLengthInf p := by
  apply le_csInf (modularSimpleGeodesicLengthSet_nonempty p hp)
  intro L hL
  exact hL.1.le

/-- The canonical simple geodesic gives the upper bound for the geometric
infimum. `PrimitiveSimpleGeodesicLengthAgreement` proves equality. -/
theorem modularSimpleGeodesicLengthInf_le_trace_norm (p : ℤ × ℤ)
    (hp : IsCoprime p.1 p.2) :
    modularSimpleGeodesicLengthInf p ≤ ‖intVector traceBasis p‖ :=
  csInf_le (modularSimpleGeodesicLengthSet_bddBelow p)
    (trace_norm_mem_modularSimpleGeodesicLengthSet p hp)

end Markov
