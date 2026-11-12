import Markov.TraceBoundaryAtoms
import Markov.TraceBoundaryOpenArcs

/-! The full actual normal fibres on an open boundary arc fit between
its outgoing initial angle and incoming terminal angle. The resulting
normal diameter is bounded by the actual boundary turn mass in every
quadrant and across seams. No angular-containment or tail input is used. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace Markov

theorem traceBoundaryOpenArc_normals_subset_lift_arc (a b : ℝ)
    (ha : 0 ≤ a) (hb : b ≤ 4) :
    normalsOn traceBasis (traceBoundaryOpenArc a b) ⊆
      circleNormal '' Icc (traceCyclicAngleLift a) (Function.leftLim traceCyclicAngleLift b) := by
  rintro n ⟨x, ⟨t, ht, rfl⟩, f, hf, rfl⟩
  have htf : normalizedEuclideanCovector traceBasis f ∈
      normalsOn traceBasis {traceBoundaryPath t} :=
    ⟨traceBoundaryPath t, rfl, f, hf, rfl⟩
  rw [traceBoundaryPath_normals_eq_lift_arc t
    ⟨lt_of_le_of_lt ha ht.1, ht.2.le.trans hb⟩] at htf
  obtain ⟨θ, hθ, hnormal⟩ := htf
  exact ⟨θ, ⟨(traceCyclicAngleLift.mono.le_leftLim ht.1).trans hθ.1,
    hθ.2.trans (traceCyclicAngleLift.mono.le_leftLim ht.2)⟩, hnormal⟩

theorem traceBoundaryTurn_openArc_toReal (a b : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 4) :
    (traceBoundaryTurn (traceBoundaryOpenArc a b)).toReal =
      Function.leftLim traceCyclicAngleLift b - traceCyclicAngleLift a := by
  rw [traceBoundaryTurn_openArc_eq a b ha hb,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (traceCyclicAngleLift.mono.le_leftLim hab))]

/-- All supports on the genuine boundary arc, including supports at
corners in its interior, satisfy the actual turn bound. -/
theorem traceBoundaryOpenArc_normals_diam_le_turn (a b : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 4) :
    Metric.diam (normalsOn traceBasis (traceBoundaryOpenArc a b)) ≤
      (traceBoundaryTurn (traceBoundaryOpenArc a b)).toReal := by
  rw [traceBoundaryTurn_openArc_toReal a b ha hab hb]
  exact normalsOn_diam_le_angular_width traceBasis (traceBoundaryOpenArc a b)
    (traceCyclicAngleLift a) (Function.leftLim traceCyclicAngleLift b)
    (traceCyclicAngleLift.mono.le_leftLim hab)
    (traceBoundaryOpenArc_normals_subset_lift_arc a b ha hb)

theorem traceBoundaryOpenArc_normals_closure_diam_le_turn (a b : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 4) :
    Metric.diam (closure (normalsOn traceBasis (traceBoundaryOpenArc a b))) ≤
      (traceBoundaryTurn (traceBoundaryOpenArc a b)).toReal := by
  rw [Metric.diam_closure]
  exact traceBoundaryOpenArc_normals_diam_le_turn a b ha hab hb

end Markov
