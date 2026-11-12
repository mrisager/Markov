import Markov.AngularNormals
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! Support angles and their angular envelope, with containment
derived from the support angles themselves. -/

noncomputable section
namespace Markov
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def supportComplex (C : Module.Basis (Fin 2) ℝ E) (f : StrongDual ℝ E) : ℂ :=
  ⟨f (C 0), f (C 1)⟩

def supportAngle (C : Module.Basis (Fin 2) ℝ E) (f : StrongDual ℝ E) : ℝ :=
  Complex.arg (supportComplex C f)

theorem supportComplex_norm (C : Module.Basis (Fin 2) ℝ E) (f : StrongDual ℝ E) :
    ‖supportComplex C f‖ = ‖euclideanDualCoordinates C f‖ := by
  simp [supportComplex, Complex.norm_def, Complex.normSq_apply,
    EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.norm_eq_abs, pow_two]

theorem supportComplex_ne_zero (C : Module.Basis (Fin 2) ℝ E)
    (f : StrongDual ℝ E) (hf : f ≠ 0) : supportComplex C f ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [supportComplex_norm]
  exact norm_ne_zero_iff.mpr (euclideanDualCoordinates_ne_zero C f hf)

theorem circleNormal_supportAngle (C : Module.Basis (Fin 2) ℝ E)
    (f : StrongDual ℝ E) (hf : f ≠ 0) :
    circleNormal (supportAngle C f) = normalizedEuclideanCovector C f := by
  ext i
  fin_cases i
  · change Real.cos (supportAngle C f) = ‖euclideanDualCoordinates C f‖⁻¹ * f (C 0)
    rw [supportAngle, Complex.cos_arg (supportComplex_ne_zero C f hf), supportComplex_norm]
    simp [supportComplex, div_eq_mul_inv, mul_comm]
  · change Real.sin (supportAngle C f) = ‖euclideanDualCoordinates C f‖⁻¹ * f (C 1)
    rw [supportAngle, Complex.sin_arg, supportComplex_norm]
    simp [supportComplex, div_eq_mul_inv, mul_comm]

theorem continuous_supportComplex (C : Module.Basis (Fin 2) ℝ E) :
    Continuous (supportComplex C) := by
  have h0 := (ContinuousLinearMap.apply ℝ ℝ (C 0)).continuous
  have h1 := (ContinuousLinearMap.apply ℝ ℝ (C 1)).continuous
  convert (Complex.continuous_ofReal.comp h0).add
    ((Complex.continuous_ofReal.comp h1).mul
      (continuous_const : Continuous (fun _ : StrongDual ℝ E => Complex.I))) using 1
  funext f
  apply Complex.ext <;> simp [supportComplex]

/-- Positive evaluation on the sum ray gives a genuine continuous branch
of the support angle near that functional. -/
theorem supportAngle_continuousAt_of_sum_pos (C : Module.Basis (Fin 2) ℝ E)
    (f : StrongDual ℝ E) (hf : 0 < f (C 0) + f (C 1)) :
    ContinuousAt (supportAngle C) f := by
  apply (Complex.continuousAt_arg ?_).comp (continuous_supportComplex C).continuousAt
  by_cases h1 : f (C 1) = 0
  · exact Or.inl (by simpa only [supportComplex, h1, add_zero] using hf)
  · exact Or.inr h1

/-- These are the angles of actual norming supports of points in `S`. -/
def supportAnglesOn (C : Module.Basis (Fin 2) ℝ E) (S : Set E) : Set ℝ :=
  {θ | ∃ x ∈ S, ∃ f ∈ normingFunctionals x, θ = supportAngle C f}

theorem supportAnglesOn_bddBelow (C : Module.Basis (Fin 2) ℝ E) (S : Set E) :
    BddBelow (supportAnglesOn C S) := by
  refine ⟨-Real.pi, ?_⟩
  rintro θ ⟨x, hx, f, hf, rfl⟩
  exact (Complex.neg_pi_lt_arg _).le

theorem supportAnglesOn_bddAbove (C : Module.Basis (Fin 2) ℝ E) (S : Set E) :
    BddAbove (supportAnglesOn C S) := by
  refine ⟨Real.pi, ?_⟩
  rintro θ ⟨x, hx, f, hf, rfl⟩
  exact Complex.arg_le_pi _

theorem supportAnglesOn_nonempty (C : Module.Basis (Fin 2) ℝ E) (S : Set E)
    (hS : S.Nonempty) : (supportAnglesOn C S).Nonempty := by
  obtain ⟨x, hx⟩ := hS
  obtain ⟨f, hf⟩ := normingFunctionals_nonempty x
  exact ⟨supportAngle C f, x, hx, f, hf, rfl⟩

def supportAngleLower (C : Module.Basis (Fin 2) ℝ E) (S : Set E) : ℝ :=
  sInf (supportAnglesOn C S)

def supportAngleUpper (C : Module.Basis (Fin 2) ℝ E) (S : Set E) : ℝ :=
  sSup (supportAnglesOn C S)

theorem supportAngleLower_le_upper (C : Module.Basis (Fin 2) ℝ E) (S : Set E)
    (hS : S.Nonempty) : supportAngleLower C S ≤ supportAngleUpper C S := by
  obtain ⟨θ, hθ⟩ := supportAnglesOn_nonempty C S hS
  exact (csInf_le (supportAnglesOn_bddBelow C S) hθ).trans
    (le_csSup (supportAnglesOn_bddAbove C S) hθ)

/-- The actual unit-boundary normals are contained in the closed envelope
of their actual support angles. No interval-containment premise is used. -/
theorem normalsOn_subset_supportAngle_envelope (C : Module.Basis (Fin 2) ℝ E)
    (S : Set E) (hS : ∀ x ∈ S, ‖x‖ = 1) :
    normalsOn C S ⊆ circleNormal '' Set.Icc (supportAngleLower C S) (supportAngleUpper C S) := by
  rintro n ⟨x, hx, f, hf, rfl⟩
  have hne : x ≠ 0 := by intro hz; simpa [hz] using hS x hx
  have hfne := normingFunctional_ne_zero x hne f hf
  have hθ : supportAngle C f ∈ supportAnglesOn C S := ⟨x, hx, f, hf, rfl⟩
  exact ⟨supportAngle C f,
    ⟨csInf_le (supportAnglesOn_bddBelow C S) hθ,
      le_csSup (supportAnglesOn_bddAbove C S) hθ⟩,
    circleNormal_supportAngle C f hfne⟩

end Markov
