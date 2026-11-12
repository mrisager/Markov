import Markov.TraceCornerTurn

/-! The actual local trace turn controls the genuine normal set of an
open radial section. The enclosing angle interval is derived from all
norming supports, with the outgoing support at the left endpoint and the
incoming support at the right endpoint. The interval's angular width is
exactly the local Stieltjes mass of the open parameter interval. No global
cyclic identification or exponential turn estimate is asserted here. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace Markov

/-- All actual supports at strictly ordered trace parameters have the
corresponding order of angles on the proved common angle branch. -/
theorem trace_supportAngle_le_of_parameter_lt
    (s t : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s < t)
    (f g : StrongDual ℝ TracePlane)
    (hf : f ∈ normingFunctionals (traceBasis 0 + s • traceBasis 1))
    (hg : g ∈ normingFunctionals (traceBasis 0 + t • traceBasis 1)) :
    supportAngle traceBasis f ≤ supportAngle traceBasis g := by
  apply normingSupport_basisLine_supportAngle_le traceBasis s t hst f g hf hg
  · simpa only [map_add] using trace_normingFunctional_sum_pos_Icc s hs f hf
  · simpa only [map_add] using trace_normingFunctional_sum_pos_Icc t ht g hg

/-- The outgoing angle at the left endpoint is at most the incoming
angle at the right endpoint of every nonempty local parameter interval. -/
theorem trace_selectedAngle_le_leftSelectedAngle_of_lt
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    traceSelectedAngle a ≤ traceLeftSelectedAngle b :=
  trace_supportAngle_le_of_parameter_lt a b ⟨ha, hab.le.trans hb⟩
    ⟨ha.trans hab.le, hb⟩ hab _ _
    (selectedAffineSupport_mem_normingFunctionals traceBasis a)
    (leftSelectedAffineSupport_mem_normingFunctionals traceBasis b)

/-- Every actual support normal of this open boundary section belongs
to the interval between its outgoing and incoming endpoint angles. The
angular containment is proved from support geometry. -/
theorem trace_openArc_normals_subset_endpoint_angle_arc
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    normalsOn traceBasis (slopeBoundaryArc traceBasis a b) ⊆
      circleNormal '' Icc (traceSelectedAngle a) (traceLeftSelectedAngle b) := by
  rw [normalsOn_slopeBoundaryArc]
  rintro n ⟨f, ⟨t, ht, hf⟩, rfl⟩
  have htf : f ∈ normingFunctionals (traceBasis 0 + t • traceBasis 1) := by
    rwa [radialBasisSection,
      normingFunctionals_normalize_eq _ (basis_affineLine_ne_zero traceBasis t)] at hf
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ha.trans ht.1.le, ht.2.le.trans hb⟩
  refine ⟨supportAngle traceBasis f, ⟨?_, ?_⟩, ?_⟩
  · exact trace_supportAngle_le_of_parameter_lt a t ⟨ha, hab.le.trans hb⟩
      htI ht.1 _ f (selectedAffineSupport_mem_normingFunctionals traceBasis a) htf
  · exact trace_supportAngle_le_of_parameter_lt t b htI ⟨ha.trans hab.le, hb⟩
      ht.2 f _ htf (leftSelectedAffineSupport_mem_normingFunctionals traceBasis b)
  · exact circleNormal_supportAngle traceBasis f
      (normingFunctional_ne_zero _ (basis_affineLine_ne_zero traceBasis t) f htf)

/-- The actual turn of an open local parameter interval omits both
endpoint corner atoms. Its exact width uses the incoming right endpoint
and outgoing left endpoint supports. -/
theorem traceQuarterTurnMeasure_Ioo_eq_endpoint_angles
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    traceQuarterTurnMeasure (Ioo a b) =
      ENNReal.ofReal (traceLeftSelectedAngle b - traceSelectedAngle a) := by
  change angleTurnMeasure traceQuarterAngleLift (Ioo a b) = _
  rw [angleTurnMeasure_Ioo]
  change ENNReal.ofReal (Function.leftLim traceQuarterAngle b - traceQuarterAngle a) = _
  rw [traceQuarterAngle_leftLim b ⟨lt_of_le_of_lt ha hab, hb⟩]
  simp only [traceQuarterAngle, quarterClamp_eq_self a ⟨ha, hab.le.trans hb⟩]

theorem traceQuarterTurnMeasure_Ioo_toReal_eq_endpoint_angles
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    (traceQuarterTurnMeasure (Ioo a b)).toReal =
      traceLeftSelectedAngle b - traceSelectedAngle a := by
  rw [traceQuarterTurnMeasure_Ioo_eq_endpoint_angles a b ha hab hb,
    ENNReal.toReal_ofReal (sub_nonneg.mpr
      (trace_selectedAngle_le_leftSelectedAngle_of_lt a b ha hab hb))]

/-- The genuine normal diameter on an actual open trace boundary arc is
at most its actual local turn measure, without an angular containment
premise or any quantitative tail hypothesis. -/
theorem trace_openArc_normals_diam_le_turn
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    Metric.diam (normalsOn traceBasis (slopeBoundaryArc traceBasis a b)) ≤
      (traceQuarterTurnMeasure (Ioo a b)).toReal := by
  rw [traceQuarterTurnMeasure_Ioo_toReal_eq_endpoint_angles a b ha hab hb]
  exact normalsOn_diam_le_angular_width traceBasis (slopeBoundaryArc traceBasis a b)
    (traceSelectedAngle a) (traceLeftSelectedAngle b)
    (trace_selectedAngle_le_leftSelectedAngle_of_lt a b ha hab hb)
    (trace_openArc_normals_subset_endpoint_angle_arc a b ha hab hb)

/-- Taking the closure of the genuine normal set retains the same
diameter bound, so the local turn also controls endpoint limit normals. -/
theorem trace_openArc_normals_closure_diam_le_turn
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    Metric.diam (closure (normalsOn traceBasis (slopeBoundaryArc traceBasis a b))) ≤
      (traceQuarterTurnMeasure (Ioo a b)).toReal := by
  rw [Metric.diam_closure]
  exact trace_openArc_normals_diam_le_turn a b ha hab hb

end Markov
