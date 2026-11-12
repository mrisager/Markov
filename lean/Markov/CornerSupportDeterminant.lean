import Markov.BoundaryAtomDeterminant

/-! Exact determinant identities for two actual supports over an integral
sum direction. These identities turn a jump in a support evaluation into
the determinant used in the lower bound for a boundary turn atom. -/

noncomputable section

namespace Markov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Evaluating two real covectors on an integral pair multiplies their
coordinate determinant by the determinant of that pair. -/
theorem euclideanDualCoordinates_det_basis_identity
    (B : Module.Basis (Fin 2) ℝ E) (f g : StrongDual ℝ E) (u v : ℤ × ℤ) :
    euclideanPlaneDet (euclideanDualCoordinates B f) (euclideanDualCoordinates B g) *
        (intDet u v : ℝ) =
      f (intVector B u) * g (intVector B v) -
        f (intVector B v) * g (intVector B u) := by
  simp [euclideanPlaneDet, intVector, intDet]
  ring

/-- When two functionals have the same value on the sum direction, their
determinant is that value times the difference of their first evaluations. -/
theorem euclideanDualCoordinates_det_mul_intDet_of_common_value
    (B : Module.Basis (Fin 2) ℝ E) (f g : StrongDual ℝ E) (u v : ℤ × ℤ)
    (L : ℝ) (hf : f (intVector B (u + v)) = L)
    (hg : g (intVector B (u + v)) = L) :
    euclideanPlaneDet (euclideanDualCoordinates B f) (euclideanDualCoordinates B g) *
        (intDet u v : ℝ) =
      L * (f (intVector B u) - g (intVector B u)) := by
  rw [euclideanDualCoordinates_det_basis_identity]
  have hsum : intVector B (u + v) = intVector B u + intVector B v := by
    simp only [intVector, Prod.fst_add, Prod.snd_add, Int.cast_add, add_smul]
    module
  rw [hsum, map_add] at hf hg
  have hfv : f (intVector B v) = L - f (intVector B u) := by linarith
  have hgv : g (intVector B v) = L - g (intVector B u) := by linarith
  rw [hfv, hgv]
  ring

/-- The absolute identity for a unimodular pair, without sign conventions
on either the integral basis or the difference of evaluations. -/
theorem euclideanDualCoordinates_det_abs_of_common_value
    (B : Module.Basis (Fin 2) ℝ E) (f g : StrongDual ℝ E) (u v : ℤ × ℤ)
    (hdet : |intDet u v| = 1) (L : ℝ)
    (hf : f (intVector B (u + v)) = L)
    (hg : g (intVector B (u + v)) = L) :
    |euclideanPlaneDet (euclideanDualCoordinates B f) (euclideanDualCoordinates B g)| =
      |L| * |f (intVector B u) - g (intVector B u)| := by
  have h := congrArg abs
    (euclideanDualCoordinates_det_mul_intDet_of_common_value B f g u v L hf hg)
  have hdet' : |(intDet u v : ℝ)| = 1 := by exact_mod_cast hdet
  simpa only [abs_mul, hdet', mul_one] using h

/-- Two genuine norming supports at a unimodular sum have determinant
equal to the norm of that sum times their evaluation jump. -/
theorem normingSupport_det_abs_of_unimodular_sum
    (B : Module.Basis (Fin 2) ℝ E) (u v : ℤ × ℤ) (hdet : |intDet u v| = 1)
    (f g : StrongDual ℝ E)
    (hf : f ∈ normingFunctionals (intVector B (u + v)))
    (hg : g ∈ normingFunctionals (intVector B (u + v))) :
    |euclideanPlaneDet (euclideanDualCoordinates B f) (euclideanDualCoordinates B g)| =
      ‖intVector B (u + v)‖ * |f (intVector B u) - g (intVector B u)| := by
  simpa only [abs_of_nonneg (norm_nonneg _)] using
    euclideanDualCoordinates_det_abs_of_common_value B f g u v hdet
      ‖intVector B (u + v)‖ hf.2 hg.2

/-- Named-jump version of the exact norming-support determinant identity. -/
theorem normingSupport_det_abs_of_jump
    (B : Module.Basis (Fin 2) ℝ E) (u v : ℤ × ℤ) (hdet : |intDet u v| = 1)
    (f g : StrongDual ℝ E)
    (hf : f ∈ normingFunctionals (intVector B (u + v)))
    (hg : g ∈ normingFunctionals (intVector B (u + v)))
    (J : ℝ) (hJ : f (intVector B u) - g (intVector B u) = J) :
    |euclideanPlaneDet (euclideanDualCoordinates B f) (euclideanDualCoordinates B g)| =
      ‖intVector B (u + v)‖ * |J| := by
  rw [normingSupport_det_abs_of_unimodular_sum B u v hdet f g hf hg, hJ]

/-- At either vector of an integral unimodular pair, the support determinant
is the norm of that vector times the jump on its partner. -/
theorem normingSupport_det_abs_of_unimodular_direction
    (B : Module.Basis (Fin 2) ℝ E) (p q : ℤ × ℤ) (hdet : |intDet p q| = 1)
    (f g : StrongDual ℝ E)
    (hf : f ∈ normingFunctionals (intVector B p))
    (hg : g ∈ normingFunctionals (intVector B p)) :
    |euclideanPlaneDet (euclideanDualCoordinates B f) (euclideanDualCoordinates B g)| =
      ‖intVector B p‖ * |f (intVector B q) - g (intVector B q)| := by
  have h := euclideanDualCoordinates_det_basis_identity B f g p q
  rw [hf.2, hg.2] at h
  have hid : ‖intVector B p‖ * g (intVector B q) -
      f (intVector B q) * ‖intVector B p‖ =
      -(‖intVector B p‖ * (f (intVector B q) - g (intVector B q))) := by ring
  rw [hid] at h
  have ha := congrArg abs h
  have hdet' : |(intDet p q : ℝ)| = 1 := by exact_mod_cast hdet
  simpa only [abs_mul, hdet', mul_one, abs_neg, abs_of_nonneg (norm_nonneg _)] using ha

/-- Named-jump version for any unimodular direction and partner. -/
theorem normingSupport_det_abs_of_direction_jump
    (B : Module.Basis (Fin 2) ℝ E) (p q : ℤ × ℤ) (hdet : |intDet p q| = 1)
    (f g : StrongDual ℝ E)
    (hf : f ∈ normingFunctionals (intVector B p))
    (hg : g ∈ normingFunctionals (intVector B p))
    (J : ℝ) (hJ : f (intVector B q) - g (intVector B q) = J) :
    |euclideanPlaneDet (euclideanDualCoordinates B f) (euclideanDualCoordinates B g)| =
      ‖intVector B p‖ * |J| := by
  rw [normingSupport_det_abs_of_unimodular_direction B p q hdet f g hf hg, hJ]

/-- A support jump on a unimodular partner gives a lower bound for the
actual atom in any integral direction, including coordinate axes. -/
theorem traceBoundaryTurn_atom_lower_of_direction_support_jump
    (p q : ℤ × ℤ) (hdet : |intDet p q| = 1)
    (hne : intVector traceBasis p ≠ 0)
    (f g : StrongDual ℝ TracePlane)
    (hf : f ∈ normingFunctionals (intVector traceBasis p))
    (hg : g ∈ normingFunctionals (intVector traceBasis p))
    (J : ℝ) (hJ : f (intVector traceBasis q) - g (intVector traceBasis q) = J) :
    ‖intVector traceBasis p‖ * |J| / (‖traceBasis 0‖ + ‖traceBasis 1‖) ^ 2 ≤
      (traceBoundaryTurn {NormedSpace.normalize (intVector traceBasis p)}).toReal := by
  have hfn : f ∈ normingFunctionals (NormedSpace.normalize (intVector traceBasis p)) := by
    rwa [normingFunctionals_normalize_eq _ hne]
  have hgn : g ∈ normingFunctionals (NormedSpace.normalize (intVector traceBasis p)) := by
    rwa [normingFunctionals_normalize_eq _ hne]
  have h := traceBoundaryTurn_atom_lower_of_norming_det
    (NormedSpace.normalize (intVector traceBasis p))
    (NormedSpace.norm_normalize hne) f g hfn hgn
  rwa [normingSupport_det_abs_of_direction_jump traceBasis p q hdet f g hf hg J hJ] at h

/-- A support-evaluation jump gives a lower bound for the actual atom at
the normalized sum direction. -/
theorem traceBoundaryTurn_atom_lower_of_support_jump
    (u v : ℤ × ℤ) (hdet : |intDet u v| = 1)
    (hne : intVector traceBasis (u + v) ≠ 0)
    (f g : StrongDual ℝ TracePlane)
    (hf : f ∈ normingFunctionals (intVector traceBasis (u + v)))
    (hg : g ∈ normingFunctionals (intVector traceBasis (u + v)))
    (J : ℝ) (hJ : f (intVector traceBasis u) - g (intVector traceBasis u) = J) :
    ‖intVector traceBasis (u + v)‖ * |J| / (‖traceBasis 0‖ + ‖traceBasis 1‖) ^ 2 ≤
      (traceBoundaryTurn {NormedSpace.normalize (intVector traceBasis (u + v))}).toReal := by
  have hfn : f ∈ normingFunctionals
      (NormedSpace.normalize (intVector traceBasis (u + v))) := by
    rwa [normingFunctionals_normalize_eq _ hne]
  have hgn : g ∈ normingFunctionals
      (NormedSpace.normalize (intVector traceBasis (u + v))) := by
    rwa [normingFunctionals_normalize_eq _ hne]
  have h := traceBoundaryTurn_atom_lower_of_norming_det
    (NormedSpace.normalize (intVector traceBasis (u + v)))
    (NormedSpace.norm_normalize hne) f g hfn hgn
  rwa [normingSupport_det_abs_of_jump traceBasis u v hdet f g hf hg J hJ] at h

end Markov
