import Markov.QuadrantCoverage
import Markov.SeededSeparation
import Markov.SupportShear

/-! Uniform separation for all integral unimodular directions, relative to
the explicit geometric norm/trace property on the four concrete seeds.
No restriction to a single Farey sector or to the original partner's height
is needed: bounded partners and shear invariance are proved. -/

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isCoprime_of_intDet_one (u v : ℤ × ℤ) (hd : intDet u v = 1) :
    IsCoprime u.1 u.2 := by
  refine ⟨v.2, -v.1, ?_⟩
  dsimp [intDet] at hd
  nlinarith

theorem isCoprime_of_intDet_neg_one (u v : ℤ × ℤ) (hd : intDet u v = -1) :
    IsCoprime u.1 u.2 := by
  refine ⟨-v.2, v.1, ?_⟩
  dsimp [intDet] at hd
  nlinarith

/-- The global positive-orientation estimate under norm–trace
compatibility. `TraceSeparation` supplies the constructed-norm instance. -/
theorem selectedSupport_global_lower_bound_pos (B : Module.Basis (Fin 2) ℝ E)
    (htrace : QuadrantTraceLengthCompatible B) (u v d : ℤ × ℤ) (A : ℝ)
    (hA : 1 ≤ A) (hu : intHeight u ≤ A) (hdet : intDet u v = 1)
    (hd : d ≠ (0, 0)) :
    Real.exp (-(planeSeparationConstant B * intEuclidean d * A ^ 2)) ≤
      |integralCovectorDet (dualCoordinates B (selectedSupportAt B u v)) d| := by
  obtain ⟨k, q, M, N, hw, hq⟩ := primitive_exists_quadrantSeededFarey_left u
    (isCoprime_of_intDet_one u v hdet)
  have hdq : intDet u q = 1 := hw.det_eq_seed.trans (quadrantSeed_det_eq_one k)
  rw [selectedSupportAt_eq_of_unimodular B u v q hdet hdq]
  exact hw.quadrant_separation B htrace k d A hA hu (by linarith [hq.trans hu]) hd

/-- The global negative-orientation estimate, using a bounded partner on
the opposite side and the reversed matrix-ray calculation. -/
theorem selectedSupport_global_lower_bound_neg (B : Module.Basis (Fin 2) ℝ E)
    (htrace : QuadrantTraceLengthCompatible B) (u v d : ℤ × ℤ) (A : ℝ)
    (hA : 1 ≤ A) (hu : intHeight u ≤ A) (hdet : intDet u v = -1)
    (hd : d ≠ (0, 0)) :
    Real.exp (-(planeSeparationConstant B * intEuclidean d * A ^ 2)) ≤
      |integralCovectorDet (dualCoordinates B (selectedSupportAt B u v)) d| := by
  obtain ⟨k, q, M, N, hw, hq⟩ := primitive_exists_quadrantSeededFarey_right u
    (isCoprime_of_intDet_neg_one u v hdet)
  have hqu : intDet q u = 1 := hw.det_eq_seed.trans (quadrantSeed_det_eq_one k)
  have hdq : intDet u q = -1 := by dsimp [intDet] at *; nlinarith
  rw [selectedSupportAt_eq_of_neg_unimodular B u v q hdet hdq]
  exact hw.quadrant_reversed_separation B htrace k d A hA hu (by linarith [hq.trans hu]) hd

/-- Lemma 5's arithmetic separation in every integral direction, relative
to the explicitly stated geometric compatibility. Its uniform constant is
independent of the chosen directions and their original Farey partners. -/
theorem selectedSupport_global_lower_bound (B : Module.Basis (Fin 2) ℝ E)
    (htrace : QuadrantTraceLengthCompatible B) (u v d : ℤ × ℤ) (A : ℝ)
    (hA : 1 ≤ A) (hu : intHeight u ≤ A) (hdet : |intDet u v| = 1)
    (hd : d ≠ (0, 0)) :
    Real.exp (-(planeSeparationConstant B * intEuclidean d * A ^ 2)) ≤
      |integralCovectorDet (dualCoordinates B (selectedSupportAt B u v)) d| := by
  have horient : intDet u v = 1 ∨ intDet u v = -1 := by
    rcases le_total 0 (intDet u v) with hp | hn
    · rw [abs_of_nonneg hp] at hdet
      exact Or.inl hdet
    · rw [abs_of_nonpos hn] at hdet
      exact Or.inr (by omega)
  rcases horient with hp | hn
  · exact selectedSupport_global_lower_bound_pos B htrace u v d A hA hu hp hd
  · exact selectedSupport_global_lower_bound_neg B htrace u v d A hA hu hn hd

/-- A relative nonvanishing corollary with no height parameter. -/
theorem selectedSupport_global_det_ne_zero (B : Module.Basis (Fin 2) ℝ E)
    (htrace : QuadrantTraceLengthCompatible B) (u v d : ℤ × ℤ)
    (hdet : |intDet u v| = 1) (hd : d ≠ (0, 0)) :
    integralCovectorDet (dualCoordinates B (selectedSupportAt B u v)) d ≠ 0 := by
  have h := selectedSupport_global_lower_bound B htrace u v d (max 1 (intHeight u))
    (le_max_left _ _) (le_max_right _ _) hdet hd
  intro hz
  rw [hz, abs_zero] at h
  exact (not_le_of_gt (Real.exp_pos _)) h

end Markov
