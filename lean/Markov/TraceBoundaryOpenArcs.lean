import Markov.TraceBoundaryCoverage
import Markov.TraceBoundaryInjective
import Markov.TraceBoundaryTurn
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Open arcs of the actual trace boundary are the images of open
parameter intervals in one traversal. Their exact preimages follow from
the proved injectivity, and their Borel measurability follows from the
Lusin--Souslin theorem. Consequently their transported turn masses are
exactly the actual Stieltjes masses of those open parameter intervals. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace Markov

/-- The actual boundary arc with both parameter endpoints omitted. -/
def traceBoundaryOpenArc (a b : ℝ) : Set TracePlane :=
  traceBoundaryPath '' Ioo a b

theorem traceBoundaryOpenArc_subset_frontier (a b : ℝ) :
    traceBoundaryOpenArc a b ⊆ frontier (Metric.closedBall (0 : TracePlane) 1) := by
  rintro x ⟨t, _, rfl⟩
  exact traceBoundaryPath_mem_frontier t

private theorem Ioo_subset_traceBoundaryPeriod (a b : ℝ)
    (ha : 0 ≤ a) (hb : b ≤ 4) : Ioo a b ⊆ Ioc (0 : ℝ) 4 := by
  intro t ht
  exact ⟨lt_of_le_of_lt ha ht.1, ht.2.le.trans hb⟩

/-- Removing both arc endpoints gives precisely the open parameter
interval inside the half-open single-traversal period. -/
theorem traceBoundaryPath_preimage_openArc_inter_Ioc (a b : ℝ)
    (ha : 0 ≤ a) (hb : b ≤ 4) :
    traceBoundaryPath ⁻¹' traceBoundaryOpenArc a b ∩ Ioc (0 : ℝ) 4 = Ioo a b := by
  exact traceBoundaryPath_injOn_Ioc.preimage_image_inter
    (Ioo_subset_traceBoundaryPeriod a b ha hb)

/-- An open parameter arc has a Borel image in the actual trace plane. -/
theorem measurableSet_traceBoundaryOpenArc (a b : ℝ)
    (ha : 0 ≤ a) (hb : b ≤ 4) : MeasurableSet (traceBoundaryOpenArc a b) := by
  letI : FiniteDimensional ℝ TracePlane := traceBasis.finiteDimensional_of_finite
  letI : ProperSpace TracePlane := FiniteDimensional.proper ℝ TracePlane
  exact measurableSet_Ioo.image_of_measurable_injOn measurable_traceBoundaryPath
    (traceBoundaryPath_injOn_Ioc.mono (Ioo_subset_traceBoundaryPeriod a b ha hb))

/-- The actual open boundary arc carries exactly its parameter interval's
Stieltjes turn, with both endpoint atoms omitted. -/
theorem traceBoundaryTurn_openArc (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 4) :
    traceBoundaryTurn (traceBoundaryOpenArc a b) =
      angleTurnMeasure traceCyclicAngleLift (Ioo a b) := by
  rw [traceBoundaryTurn_apply_eq_parameter_turn _
    (measurableSet_traceBoundaryOpenArc a b ha hb),
    traceBoundaryPath_preimage_openArc_inter_Ioc a b ha hb]

/-- The mass of an actual open boundary arc is the difference between
the terminal left angle limit and the initial angle value. -/
theorem traceBoundaryTurn_openArc_eq (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 4) :
    traceBoundaryTurn (traceBoundaryOpenArc a b) =
      ENNReal.ofReal (Function.leftLim traceCyclicAngleLift b - traceCyclicAngleLift a) := by
  rw [traceBoundaryTurn_openArc a b ha hb, angleTurnMeasure_Ioo]

end Markov
