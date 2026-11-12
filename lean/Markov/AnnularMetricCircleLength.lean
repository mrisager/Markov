import Markov.CanonicalAnnularFreeClass
import Markov.MetricCircleLengthFromHomotopy

noncomputable section
open Topology
namespace Markov

/-- Actual positive rescaling of the normalized circle to the supplied metric period. -/
def modularMetricCircleNormalize (L : ℝ) (hL : 0 < L)
    (q : C(AddCircle L, ModularTraceQuotient)) : C(NormalizedCircle, ModularTraceQuotient) :=
  q.comp ⟨AddCircle.homeomorphAddCircle (1 : ℝ) L (by norm_num) hL.ne',
    (AddCircle.homeomorphAddCircle (1 : ℝ) L (by norm_num) hL.ne').continuous⟩

theorem modularMetricCircleNormalize_coe (L : ℝ) (hL : 0 < L)
    (q : C(AddCircle L, ModularTraceQuotient)) (t : ℝ) :
    modularMetricCircleNormalize L hL q (t : NormalizedCircle) = q ((t*L : ℝ) : AddCircle L) := by
  simp [modularMetricCircleNormalize, AddCircle.homeomorphAddCircle_apply_mk]

theorem modularMetricCircleNormalize_zero (L : ℝ) (hL : 0 < L)
    (q : C(AddCircle L, ModularTraceQuotient)) : modularMetricCircleNormalize L hL q 0 = q 0 := by
  simpa only [AddCircle.coe_zero, zero_mul] using modularMetricCircleNormalize_coe L hL q 0

/-- The normalized positive parameter is literally the actual supplied
metric circle's positive once-around loop, including its orientation. -/
theorem modularMetricCircleNormalize_positiveLoop (L : ℝ) (hL : 0 < L)
    (q : C(AddCircle L, ModularTraceQuotient)) (t : unitInterval) :
    (normalizedCircleStandardLoop.map (modularMetricCircleNormalize L hL q).continuous) t =
      modularMetricCirclePositiveLoop L q t := by
  change modularMetricCircleNormalize L hL q (normalizedCircleStandardLoop t) = _
  rw [normalizedCircleStandardLoop_apply, modularMetricCircleNormalize_coe,
    modularMetricCirclePositiveLoop_apply]

theorem modularMetricCircleNormalize_original_H1 (L : ℝ) (hL : 0 < L)
    (q : C(AddCircle L, ModularTraceQuotient)) :
    modularTraceFixedSingularH1Equiv (singularLoopClass ModularTraceQuotient
      (normalizedCircleStandardLoop.map (modularMetricCircleNormalize L hL q).continuous)) =
      modularTraceFixedSingularH1Equiv
        (singularLoopClass ModularTraceQuotient (modularMetricCirclePositiveLoop L q)) :=
  congrArg modularTraceFixedSingularH1Equiv
    (singularLoopClass_pointwise_eq _ _ (modularMetricCircleNormalize_positiveLoop L hL q))

/-- Actual based path algebra changes from a common-center comparison to
the connector starting at the first loop's own actual basepoint. -/
theorem basedLoop_conjugacy_rebase
    {o x y : ModularTraceQuotient} (a : Path o x) (e : Path o y)
    (ℓ : Path x x) (μ : Path y y)
    (h : ((a.trans ℓ).trans a.symm).Homotopic ((e.trans μ).trans e.symm)) :
    ((((a.symm.trans e).trans μ).trans (a.symm.trans e).symm)).Homotopic ℓ := by
  have hc {x y z : ModularTraceQuotient}
      (a : Path.Homotopic.Quotient x y) (b : Path.Homotopic.Quotient y z) :
      a.symm.trans (a.trans b) = b := by
    rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
      Path.Homotopic.Quotient.refl_trans]
  have hh := congrArg
    (fun ν : Path.Homotopic.Quotient o o =>
      ((Path.Homotopic.Quotient.mk a.symm).trans ν).trans (.mk a))
    (Path.Homotopic.Quotient.eq.mpr h)
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc, hc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.trans_refl] at hh
  apply Path.Homotopic.Quotient.eq.mp
  simpa only [Path.trans_symm, Path.symm_symm, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm, Path.Homotopic.Quotient.trans_assoc] using hh.symm

/-- An ACTUALLY annular locally unit-speed metric circle in the original
primitive H1 class has the canonical trace-norm period. Rescaling, containment,
actual homotopies and connectors are all constructed; containment stays explicit. -/
theorem modularMetricCircle_length_eq_trace_norm_of_annular_containment
    (k : Fin 4) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection (quadrantCoordinates k p))
    (L : ℝ) (hL : 0 < L) (q : C(AddCircle L, ModularTraceQuotient))
    (hloc : ∀ t : ℝ, ∃ r > 0, ∀ s ∈ Metric.ball t r, ∀ u ∈ Metric.ball t r,
      dist (q (s : AddCircle L)) (q (u : AddCircle L)) = dist s u)
    (hcontain : ∀ u : AddCircle L, standardTorusSecondDual (originalToStandardCircleLabel p)
      (modularTraceQuotientPuncturedTorusHomeomorph (q u)).val ≠ 0)
    (hclass : modularTraceFixedSingularH1Equiv
      (singularLoopClass ModularTraceQuotient (modularMetricCirclePositiveLoop L q)) = p) :
    L = ‖intVector traceBasis p‖ := by
  let Q := modularMetricCircleNormalize L hL q
  have hQcontain : ∀ u, standardTorusSecondDual (originalToStandardCircleLabel p)
      (modularTraceQuotientPuncturedTorusHomeomorph (Q u)).val ≠ 0 :=
    fun u => hcontain _
  have hQclass : modularTraceFixedSingularH1Equiv
      (singularLoopClass ModularTraceQuotient (normalizedCircleStandardLoop.map Q.continuous)) = p :=
    (modularMetricCircleNormalize_original_H1 L hL q).trans hclass
  obtain ⟨e, he⟩ := modularCircleMap_annular_canonical_homotopy k p hp Q hQcontain hQclass
  rw [paperPrimitiveAxisTransportLoop_eq_conjugate] at he
  have hrebase := basedLoop_conjugacy_rebase (paperPrimitiveAxisProjectedConnector k p hp) e
    (modularClosedGeodesicLoop (paperPrimitiveHolonomy k p hp)
      (paperPrimitiveHolonomy_hyperbolic k p hp))
    (normalizedCircleStandardLoop.map Q.continuous) he
  let cN := (paperPrimitiveAxisProjectedConnector k p hp).symm.trans e
  let c : Path (paperPrimitiveClosedGeodesic k p hp 0) (q 0) :=
    cN.cast rfl (modularMetricCircleNormalize_zero L hL q).symm
  have hloops : ((c.trans (modularMetricCirclePositiveLoop L q)).trans c.symm) =
      ((cN.trans (normalizedCircleStandardLoop.map Q.continuous)).trans cN.symm) := by
    ext t
    simp only [c, Path.cast_coe, Path.trans_apply, Path.symm_apply]
    split_ifs
    · rfl
    · exact (modularMetricCircleNormalize_positiveLoop L hL q _).symm
    · rfl
  apply modularMetricCircle_length_eq_trace_norm_of_canonical_loop_homotopy
    k p hp L hL q hloc c
  rw [hloops]
  exact hrebase

end Markov
