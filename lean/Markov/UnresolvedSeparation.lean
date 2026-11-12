import Markov.GlobalSeparation
import Markov.UnresolvedSizes

/-! The arithmetic and logarithmic parts of Lemma 6 assembled. The angular
normal-turn estimate and Farey arc estimate remain explicit geometric inputs;
neither is declared as an axiom or claimed proved here. -/

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Endpoint-height estimate from the checked global separation theorem
and the explicit geometric determinant upper bound. -/
theorem unresolved_direction_height (B : Module.Basis (Fin 2) ℝ E)
    (htrace : QuadrantTraceLengthCompatible B) (u v d : ℤ × ℤ) (A L c H : ℝ)
    (hA : 1 ≤ A) (hu : intHeight u ≤ A) (hdet : |intDet u v| = 1)
    (hd : d ≠ (0, 0)) (hL : 1 ≤ L) (hc : 0 < c)
    (hupper : |integralCovectorDet (dualCoordinates B (selectedSupportAt B u v)) d| ≤
      L * intEuclidean d * Real.exp (-c * H)) :
    0 < (planeSeparationConstant B + Real.log L + 1) / c ∧
      H ≤ ((planeSeparationConstant B + Real.log L + 1) / c) * intEuclidean d * A ^ 2 := by
  apply unresolved_height_bound _ _ _ _ _ _ _ (intEuclidean_ge_one d hd) hA hL
    (planeSeparationConstant_pos B).le hc _ hupper
  simpa only [neg_mul] using selectedSupport_global_lower_bound B htrace u v d A hA hu hdet hd

/-- The unresolved arc scale of v1 Lemma 6 under the displayed
geometric hypotheses. -/
theorem unresolved_direction_arc_bound (B : Module.Basis (Fin 2) ℝ E)
    (htrace : QuadrantTraceLengthCompatible B) (u v d : ℤ × ℤ) (A L c H C s : ℝ)
    (hA : 1 ≤ A) (hu : intHeight u ≤ A) (hdet : |intDet u v| = 1)
    (hd : d ≠ (0, 0)) (hL : 1 ≤ L) (hc : 0 < c)
    (hH : 0 < H) (hC : 0 ≤ C) (hs0 : 0 ≤ s)
    (hupper : |integralCovectorDet (dualCoordinates B (selectedSupportAt B u v)) d| ≤
      L * intEuclidean d * Real.exp (-c * H)) (hs : s ≤ C / (H * A)) :
    s ≤ C * Real.sqrt ((planeSeparationConstant B + Real.log L + 1) / c) *
      Real.sqrt (intEuclidean d) / (H * Real.sqrt H) := by
  apply unresolved_cap_arc_bound _ _ _ _ _ _ _ _ _ (intEuclidean_ge_one d hd) hA hL
    (planeSeparationConstant_pos B).le hc hH hC hs0 _ hupper hs
  simpa only [neg_mul] using selectedSupport_global_lower_bound B htrace u v d A hA hu hdet hd

end Markov
