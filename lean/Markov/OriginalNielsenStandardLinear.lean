import Markov.OriginalMarkedNielsenRight

/-! Coordinate formulas for the original-marked Nielsen homeomorphisms.
The linear Farey witnesses use these maps in the standard torus model. -/

noncomputable section
namespace Markov

/-- The actual inverse original Nielsen chart is the actual signed swap of
the actual fixed punctured-torus coordinate map. -/
theorem originalNielsenChart_symm_standard (z : ModularTraceQuotient) :
    (originalNielsenChart.symm z).val =
      (-(modularTraceQuotientPuncturedTorusHomeomorph z).val.2,
       -(modularTraceQuotientPuncturedTorusHomeomorph z).val.1) := rfl

/-- The ACTUAL original left-move homeomorphism has literal integer-linear
standard-coordinate formula (x,y) -> (x,x+y). No connector or word action is changed. -/
theorem originalNielsenHomeomorph_standard_linear (z : ModularTraceQuotient) :
    (modularTraceQuotientPuncturedTorusHomeomorph (originalNielsenHomeomorph z)).val =
      ((modularTraceQuotientPuncturedTorusHomeomorph z).val.1,
       (modularTraceQuotientPuncturedTorusHomeomorph z).val.1 +
        (modularTraceQuotientPuncturedTorusHomeomorph z).val.2) := by
  change (modularTraceQuotientPuncturedTorusHomeomorph
    (originalNielsenChart (surgeryColumnShear (originalNielsenChart.symm z)))).val = _
  rw [originalNielsenChart_standard]
  simp only [surgeryColumnShear_coe, originalNielsenChart_symm_standard,
    neg_add_rev, neg_neg]

/-- The right-move S-L-S homeomorphism has standard-coordinate
formula `(x, y) ↦ (x + y, y)`. -/
theorem originalNielsenRightHomeomorph_standard_linear (z : ModularTraceQuotient) :
    (modularTraceQuotientPuncturedTorusHomeomorph (originalNielsenRightHomeomorph z)).val =
      ((modularTraceQuotientPuncturedTorusHomeomorph z).val.1 +
        (modularTraceQuotientPuncturedTorusHomeomorph z).val.2,
       (modularTraceQuotientPuncturedTorusHomeomorph z).val.2) := by
  have hs (w : ModularTraceQuotient) :
      (modularTraceQuotientPuncturedTorusHomeomorph (modularCoordinateSwapHomeomorph w)).val =
        ((modularTraceQuotientPuncturedTorusHomeomorph w).val.2,
         (modularTraceQuotientPuncturedTorusHomeomorph w).val.1) := by
    rw [modularCoordinateSwapHomeomorph_standard, standardCoordinateSwapPuncturedTorusHomeomorph_coe]
  change (modularTraceQuotientPuncturedTorusHomeomorph
    (modularCoordinateSwapHomeomorph
      (originalNielsenHomeomorph (modularCoordinateSwapHomeomorph z)))).val = _
  rw [hs, originalNielsenHomeomorph_standard_linear, hs]
  exact Prod.ext (add_comm _ _) rfl

end Markov
