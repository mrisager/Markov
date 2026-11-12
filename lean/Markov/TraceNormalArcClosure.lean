import Markov.TraceBoundaryNormalAngles

/-! The closed swept normal arc is exactly the closure of the actual
normal directions over an open trace-boundary arc. A zero angular width
is included: the actual nonempty angle set then consists of one angle. -/

noncomputable section
open Set

namespace Markov

/-- A nonempty real set sandwiched between the open and closed intervals
has exactly that closed interval as its closure, including a singleton. -/
theorem closure_eq_Icc_of_interval_sandwich (S : Set ℝ) (a b : ℝ)
    (hS : S.Nonempty) (hopen : Ioo a b ⊆ S) (hclosed : S ⊆ Icc a b) :
    closure S = Icc a b := by
  apply le_antisymm
  · exact closure_minimal hclosed isClosed_Icc
  · by_cases hab : a = b
    · subst b
      intro x hx
      have hxa : x = a := le_antisymm hx.2 hx.1
      obtain ⟨y, hy⟩ := hS
      have hya : y = a := le_antisymm (hclosed hy).2 (hclosed hy).1
      subst x
      subst y
      exact subset_closure hy
    · rw [← closure_Ioo hab]
      exact closure_mono hopen

/-- The actual completed normal-angle set is dense in exactly its inward
endpoint interval, regardless of whether the angular width vanishes. -/
theorem closure_traceBoundaryNormalAngles (a b : ℝ) (hab : a < b) :
    closure (traceBoundaryNormalAngles a b) =
      Icc (traceCyclicAngleLift a) (Function.leftLim traceCyclicAngleLift b) :=
  closure_eq_Icc_of_interval_sandwich _ _ _
    (traceBoundaryNormalAngles_isConnected a b hab).1
    (Ioo_subset_traceBoundaryNormalAngles a b hab)
    (traceBoundaryNormalAngles_subset_Icc a b)

/-- The closure of all genuine support normals swept over an actual open
boundary arc is precisely its closed circular endpoint-angle arc. -/
theorem closure_normalsOn_traceBoundaryOpenArc (a b : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 4) :
    closure (normalsOn traceBasis (traceBoundaryOpenArc a b)) =
      circleNormal ''
        Icc (traceCyclicAngleLift a) (Function.leftLim traceCyclicAngleLift b) := by
  rw [traceBoundaryOpenArc_normals_eq_circle_angles a b ha hb]
  have hc : IsCompact (circleNormal ''
      Icc (traceCyclicAngleLift a) (Function.leftLim traceCyclicAngleLift b)) :=
    isCompact_Icc.image circleNormal_lipschitz.continuous
  apply le_antisymm
  · exact closure_minimal (image_mono (traceBoundaryNormalAngles_subset_Icc a b))
      hc.isClosed
  · rw [← closure_traceBoundaryNormalAngles a b hab]
    exact image_closure_subset_closure_image circleNormal_lipschitz.continuous

end Markov
