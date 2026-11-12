import Markov.TraceRationalSupports
import Markov.TraceChordArcBounds
import Markov.TraceSupportGap

/-! The turn of a rational quadrant boundary arc decays exponentially
in the two endpoint heights. The bound includes every intervening normal
fibre and continuous residual turn, with the endpoint atoms omitted. -/

noncomputable section
namespace Markov

/-- The complete open arc between the actual rational path parameters is
controlled by the actual inward integral support normals. -/
theorem SeededFarey.trace_rational_arc_turn_le_inward_distance (k : Fin 4)
    {u v : ℤ × ℤ} {M0 N0 M N : IntMatrixTwo}
    (h : SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
      M0 N0 u v M N) :
    (traceBoundaryTurn (traceBoundaryOpenArc
      (traceRationalParameter k u) (traceRationalParameter k v))).toReal ≤
      (Real.pi / 2) *
        dist (normalizedEuclideanCovector traceBasis (selectedSupportAt traceBasis u v))
          (normalizedEuclideanCovector traceBasis (selectedSupportAt traceBasis v u)) := by
  have hu := h.traceRationalQuarterParameter_left_mem_Icc
  have hv := h.traceRationalQuarterParameter_right_mem_Icc
  have hh := traceBoundaryTurn_chord_openArc_le_inward_normal_distance k
    (traceRationalQuarterParameter k u) (traceRationalQuarterParameter k v)
    hu.1 h.traceRationalQuarterParameter_lt hv.2
  have hs := h.trace_rational_inward_supports k
  rw [← hs.1, ← hs.2] at hh
  exact hh

/-- Full open-arc turn, rather than just endpoint distance, has one
uniform exponential height estimate for all actual quadrant Farey pairs
above birth height one. -/
theorem trace_rational_arc_turn_height_decay :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (k : Fin 4) (u v : ℤ × ℤ) (M N : IntMatrixTwo),
      SeededFarey (quadrantSeedDirections k).1 (quadrantSeedDirections k).2
        (quadrantSeedMatrices k).1 (quadrantSeedMatrices k).2 u v M N →
      1 < intHeight (u + v) →
      (traceBoundaryTurn (traceBoundaryOpenArc
        (traceRationalParameter k u) (traceRationalParameter k v))).toReal ≤
        C * (intHeight u + intHeight v) *
          Real.exp (-(c * (intHeight u + intHeight v))) := by
  obtain ⟨C, c, hC, hc, hgap⟩ := trace_inward_normal_gap_height_decay
  have hpi : 0 < Real.pi / 2 := by positivity
  refine ⟨(Real.pi / 2) * C, c, mul_pos hpi hC, hc, ?_⟩
  intro k u v M N h hheight
  apply (h.trace_rational_arc_turn_le_inward_distance k).trans
  convert mul_le_mul_of_nonneg_left (hgap k u v M N h hheight) hpi.le using 1
  ring

end Markov
