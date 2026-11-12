import Markov.LeftAffineSupport
import Markov.TraceLocalTurn
import Markov.SupportAngleConnected
import Mathlib.Topology.Order.LeftRightLim

/-! Geometric endpoints of the actual trace support fibre and local
Stieltjes atoms. The minimum is obtained from the decreasing parameter
direction, and the maximum from the increasing direction. For 0 < t ≤ 1
the actual local turn atom is exactly their angular difference. The
clamped initial endpoint is deliberately excluded. This does not assert
a cyclic turn measure or any exponential corner estimate. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Markov

def traceLeftSelectedAngle (t : ℝ) : ℝ :=
  supportAngle traceBasis (leftSelectedAffineSupport traceBasis t)

theorem trace_supportAngle_le_selected (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (f : StrongDual ℝ TracePlane)
    (hf : f ∈ normingFunctionals (traceBasis 0 + t • traceBasis 1)) :
    supportAngle traceBasis f ≤ traceSelectedAngle t := by
  apply (normingSupport_basisLine_sameParameter_supportAngle_le_iff traceBasis t f
    (selectedAffineSupport traceBasis t) hf
    (selectedAffineSupport_mem_normingFunctionals traceBasis t) ?_ ?_).mpr
  · exact (selectedAffineSupport_spec traceBasis t).2 f hf
  · simpa only [map_add] using trace_normingFunctional_sum_pos_Icc t ht f hf
  · simpa only [map_add] using trace_normingFunctional_sum_pos_Icc t ht
      (selectedAffineSupport traceBasis t)
      (selectedAffineSupport_mem_normingFunctionals traceBasis t)

theorem trace_leftSelectedAngle_le_supportAngle (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (f : StrongDual ℝ TracePlane)
    (hf : f ∈ normingFunctionals (traceBasis 0 + t • traceBasis 1)) :
    traceLeftSelectedAngle t ≤ supportAngle traceBasis f := by
  apply (normingSupport_basisLine_sameParameter_supportAngle_le_iff traceBasis t
    (leftSelectedAffineSupport traceBasis t) f
    (leftSelectedAffineSupport_mem_normingFunctionals traceBasis t) hf ?_ ?_).mpr
  · exact leftSelectedAffineSupport_eval_le traceBasis t f hf
  · simpa only [map_add] using trace_normingFunctional_sum_pos_Icc t ht
      (leftSelectedAffineSupport traceBasis t)
      (leftSelectedAffineSupport_mem_normingFunctionals traceBasis t)
  · simpa only [map_add] using trace_normingFunctional_sum_pos_Icc t ht f hf

theorem trace_leftSelectedAngle_le_selected (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    traceLeftSelectedAngle t ≤ traceSelectedAngle t :=
  trace_leftSelectedAngle_le_supportAngle t ht (selectedAffineSupport traceBasis t)
    (selectedAffineSupport_mem_normingFunctionals traceBasis t)

/-- Every angle between the two extreme supports is an actual support
angle at this same point. Convexity of the fibre supplies the intermediate
supports, so the angular interval is not only an enclosing bound. -/
theorem trace_corner_supportAngles_eq_Icc (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    supportAngle traceBasis '' normingFunctionals (traceBasis 0 + t • traceBasis 1) =
      Icc (traceLeftSelectedAngle t) (traceSelectedAngle t) := by
  have hc : ContinuousOn (supportAngle traceBasis)
      (normingFunctionals (traceBasis 0 + t • traceBasis 1)) := by
    intro f hf
    apply (supportAngle_continuousAt_of_sum_pos traceBasis f ?_).continuousWithinAt
    simpa only [map_add] using trace_normingFunctional_sum_pos_Icc t ht f hf
  have hconnected := (normingFunctionals_isConnected
    (traceBasis 0 + t • traceBasis 1)).image (supportAngle traceBasis) hc
  have hlo : traceLeftSelectedAngle t ∈ supportAngle traceBasis ''
      normingFunctionals (traceBasis 0 + t • traceBasis 1) :=
    ⟨leftSelectedAffineSupport traceBasis t,
      leftSelectedAffineSupport_mem_normingFunctionals traceBasis t, rfl⟩
  have hhi : traceSelectedAngle t ∈ supportAngle traceBasis ''
      normingFunctionals (traceBasis 0 + t • traceBasis 1) :=
    ⟨selectedAffineSupport traceBasis t,
      selectedAffineSupport_mem_normingFunctionals traceBasis t, rfl⟩
  ext θ
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨trace_leftSelectedAngle_le_supportAngle t ht f hf,
      trace_supportAngle_le_selected t ht f hf⟩
  · intro hθ
    exact hconnected.isPreconnected.ordConnected.out hlo hhi hθ

/-- The two actual extreme support angles bound exactly the geometric
normal arc of this point on the trace unit section. -/
theorem trace_corner_normals_eq_arc (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    normalsOn traceBasis {radialBasisSection traceBasis t} =
      circleNormal '' Icc (traceLeftSelectedAngle t) (traceSelectedAngle t) := by
  rw [← trace_corner_supportAngles_eq_Icc t ht]
  ext n
  constructor
  · rintro ⟨x, hx, f, hf, rfl⟩
    have hx : x = radialBasisSection traceBasis t := hx
    subst x
    have hfl : f ∈ normingFunctionals (traceBasis 0 + t • traceBasis 1) := by
      rwa [radialBasisSection,
        normingFunctionals_normalize_eq _ (basis_affineLine_ne_zero traceBasis t)] at hf
    exact ⟨supportAngle traceBasis f, ⟨f, hfl, rfl⟩,
      circleNormal_supportAngle traceBasis f
        (normingFunctional_ne_zero _ (basis_affineLine_ne_zero traceBasis t) f hfl)⟩
  · rintro ⟨θ, ⟨f, hf, rfl⟩, rfl⟩
    refine ⟨radialBasisSection traceBasis t, rfl, f, ?_, ?_⟩
    · rwa [radialBasisSection,
        normingFunctionals_normalize_eq _ (basis_affineLine_ne_zero traceBasis t)]
    · exact circleNormal_supportAngle traceBasis f
        (normingFunctional_ne_zero _ (basis_affineLine_ne_zero traceBasis t) f hf)

theorem traceSelectedAngle_tendsto_left (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    Tendsto traceSelectedAngle (𝓝[<] t) (𝓝 (traceLeftSelectedAngle t)) := by
  apply supportAngle_selectedAffineSupport_tendsto_left
  simpa only [map_add] using trace_normingFunctional_sum_pos_Icc t ht
    (leftSelectedAffineSupport traceBasis t)
    (leftSelectedAffineSupport_mem_normingFunctionals traceBasis t)

theorem traceQuarterAngle_tendsto_left (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    Tendsto traceQuarterAngle (𝓝[<] t) (𝓝 (traceLeftSelectedAngle t)) := by
  apply (traceSelectedAngle_tendsto_left t ⟨ht.1.le, ht.2⟩).congr'
  have hpos : ∀ᶠ s : ℝ in 𝓝[<] t, 0 < s :=
    (eventually_gt_nhds ht.1).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos, self_mem_nhdsWithin] with s hs hst
  change traceSelectedAngle s = traceSelectedAngle (quarterClamp s)
  rw [quarterClamp_eq_self s ⟨hs.le, (show s < t from hst).le.trans ht.2⟩]

/-- The left limit is identified with an actual extremal support, rather
than left as an unspecified limit value. -/
theorem traceQuarterAngle_leftLim (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    Function.leftLim traceQuarterAngle t = traceLeftSelectedAngle t :=
  leftLim_eq_of_tendsto (NeBot.ne (inferInstance : (𝓝[<] t).NeBot))
    (traceQuarterAngle_tendsto_left t ht)

/-- Every interior/right-endpoint corner atom is the difference of its
actual extreme support angles. The initial clamped endpoint is excluded. -/
theorem traceQuarterTurnMeasure_singleton_eq_corner (t : ℝ)
    (ht : t ∈ Ioc (0 : ℝ) 1) :
    traceQuarterTurnMeasure {t} =
      ENNReal.ofReal (traceSelectedAngle t - traceLeftSelectedAngle t) := by
  rw [traceQuarterTurnMeasure_singleton, traceQuarterAngle_leftLim t ht]
  simp only [traceQuarterAngle, quarterClamp_eq_self t ⟨ht.1.le, ht.2⟩]

theorem traceQuarterTurnMeasure_singleton_toReal_eq_corner (t : ℝ)
    (ht : t ∈ Ioc (0 : ℝ) 1) :
    (traceQuarterTurnMeasure {t}).toReal = traceSelectedAngle t - traceLeftSelectedAngle t := by
  rw [traceQuarterTurnMeasure_singleton_eq_corner t ht,
    ENNReal.toReal_ofReal (sub_nonneg.mpr
      (trace_leftSelectedAngle_le_selected t ⟨ht.1.le, ht.2⟩))]

/-- The local atom equals Lebesgue angular length of the exact support
angle interval just identified above. This is an actual geometric width. -/
theorem traceQuarterTurnMeasure_singleton_eq_angular_length (t : ℝ)
    (ht : t ∈ Ioc (0 : ℝ) 1) :
    traceQuarterTurnMeasure {t} =
      volume (Icc (traceLeftSelectedAngle t) (traceSelectedAngle t)) := by
  rw [traceQuarterTurnMeasure_singleton_eq_corner t ht, Real.volume_Icc]

end Markov
