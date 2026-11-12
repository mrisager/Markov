import Markov.ChordCharts

/-! Quarter rotations of actual support angles and Euclidean normals.
The real angle identity is restricted to its valid principal-argument branch;
the normal identity is valid for every nonzero support. -/

noncomputable section

namespace Markov

/-- On the closed upper half-plane, multiplying by `-I` lowers the actual
principal argument by one quarter turn. -/
theorem complex_arg_neg_I_mul_add_pi_div_two (z : ℂ) (hz : z ≠ 0)
    (him : 0 ≤ z.im) :
    Complex.arg (-Complex.I * z) + Real.pi / 2 = Complex.arg z := by
  have hlo : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr him
  have hhi := Complex.arg_le_pi z
  have hmul : (-Complex.I * z).arg = (-Complex.I).arg + z.arg := by
    apply Complex.arg_mul (neg_ne_zero.mpr Complex.I_ne_zero) hz
    rw [Complex.arg_neg_I]
    constructor <;> linarith [Real.pi_pos]
  rw [Complex.arg_neg_I] at hmul
  linarith only [hmul]

/-- The ordinary counterclockwise quarter turn in the actual Euclidean
coordinate plane. -/
def quarterTurnNormal (n : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![-n 1, n 0]

@[simp] theorem quarterTurnNormal_zero_apply (n : EuclideanSpace ℝ (Fin 2)) :
    quarterTurnNormal n 0 = -n 1 := rfl

@[simp] theorem quarterTurnNormal_one_apply (n : EuclideanSpace ℝ (Fin 2)) :
    quarterTurnNormal n 1 = n 0 := rfl

/-- Adding `π / 2` rotates the actual unit-circle normal by ninety degrees. -/
theorem circleNormal_add_pi_div_two (θ : ℝ) :
    circleNormal (θ + Real.pi / 2) = quarterTurnNormal (circleNormal θ) := by
  ext i
  fin_cases i <;> simp [Real.cos_add, Real.sin_add]

theorem quarterTurnNormal_four (n : EuclideanSpace ℝ (Fin 2)) :
    quarterTurnNormal (quarterTurnNormal (quarterTurnNormal (quarterTurnNormal n))) = n := by
  ext i
  fin_cases i <;> simp

theorem norm_quarterTurnNormal (n : EuclideanSpace ℝ (Fin 2)) :
    ‖quarterTurnNormal n‖ = ‖n‖ := by
  have hs : ‖quarterTurnNormal n‖ ^ 2 = ‖n‖ ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    ring
  nlinarith [norm_nonneg (quarterTurnNormal n), norm_nonneg n]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Rotating the coordinate basis transforms an actual covector by `-I`. -/
theorem supportComplex_quarterTurnBasis (B : Module.Basis (Fin 2) ℝ E)
    (f : StrongDual ℝ E) :
    supportComplex (quarterTurnBasis B) f = -Complex.I * supportComplex B f := by
  apply Complex.ext <;> simp [supportComplex]

theorem norm_euclideanDualCoordinates_quarterTurnBasis
    (B : Module.Basis (Fin 2) ℝ E) (f : StrongDual ℝ E) :
    ‖euclideanDualCoordinates (quarterTurnBasis B) f‖ = ‖euclideanDualCoordinates B f‖ := by
  rw [← supportComplex_norm, supportComplex_quarterTurnBasis, norm_mul]
  simp [supportComplex_norm]

/-- The branch identity holds on the whole nonzero upper half-plane. -/
theorem supportAngle_quarterTurnBasis_add_pi_div_two_of_nonneg
    (B : Module.Basis (Fin 2) ℝ E) (f : StrongDual ℝ E)
    (hf : f ≠ 0) (h1 : 0 ≤ f (B 1)) :
    supportAngle (quarterTurnBasis B) f + Real.pi / 2 = supportAngle B f := by
  unfold supportAngle
  rw [supportComplex_quarterTurnBasis]
  exact complex_arg_neg_I_mul_add_pi_div_two (supportComplex B f)
    (supportComplex_ne_zero B f hf) h1

/-- Positive evaluation on the seam ray gives the actual quarter-turn
compatibility of principal support angles. -/
theorem supportAngle_quarterTurnBasis_add_pi_div_two
    (B : Module.Basis (Fin 2) ℝ E) (f : StrongDual ℝ E)
    (h1 : 0 < f (B 1)) :
    supportAngle (quarterTurnBasis B) f + Real.pi / 2 = supportAngle B f := by
  apply supportAngle_quarterTurnBasis_add_pi_div_two_of_nonneg B f _ h1.le
  intro hf
  simp [hf] at h1

/-- In actual Euclidean coordinates, undoing the quarter-turned frame
recovers the same normalized support covector, including at zero. -/
theorem normalizedEuclideanCovector_quarterTurnBasis
    (B : Module.Basis (Fin 2) ℝ E) (f : StrongDual ℝ E) :
    quarterTurnNormal (normalizedEuclideanCovector (quarterTurnBasis B) f) =
      normalizedEuclideanCovector B f := by
  ext i
  fin_cases i <;>
    simp [normalizedEuclideanCovector, NormedSpace.normalize,
      norm_euclideanDualCoordinates_quarterTurnBasis]

/-- The actual normal compatibility is independent of the branch of the
principal argument. -/
theorem circleNormal_supportAngle_quarterTurnBasis
    (B : Module.Basis (Fin 2) ℝ E) (f : StrongDual ℝ E) (hf : f ≠ 0) :
    circleNormal (supportAngle (quarterTurnBasis B) f + Real.pi / 2) =
      normalizedEuclideanCovector B f := by
  rw [circleNormal_add_pi_div_two, circleNormal_supportAngle _ _ hf,
    normalizedEuclideanCovector_quarterTurnBasis]

/-- Four actual changes of quarter-turn frame return to the original basis. -/
theorem quarterTurnBasis_four (B : Module.Basis (Fin 2) ℝ E) :
    quarterTurnBasis (quarterTurnBasis (quarterTurnBasis (quarterTurnBasis B))) = B := by
  ext i
  fin_cases i <;> simp

theorem quarterTurnBasis_iterate_four (B : Module.Basis (Fin 2) ℝ E) :
    (quarterTurnBasis^[4]) B = B := by
  simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
    quarterTurnBasis_four B

/-- Every iterated coordinate chart represents exactly the original actual
normal after adding its quarter-turn offset. This asserts no real-angle
branch identity across an entire cycle. -/
theorem circleNormal_supportAngle_iterate_quarterTurnBasis
    (B : Module.Basis (Fin 2) ℝ E) (f : StrongDual ℝ E) (hf : f ≠ 0) (n : ℕ) :
    circleNormal (supportAngle ((quarterTurnBasis^[n]) B) f + (n : ℝ) * Real.pi / 2) =
      normalizedEuclideanCovector B f := by
  induction n generalizing B with
  | zero => simpa using circleNormal_supportAngle B f hf
  | succ n ih =>
      have hangle : (n.succ : ℝ) * Real.pi / 2 = (n : ℝ) * Real.pi / 2 + Real.pi / 2 := by
        push_cast
        ring
      rw [Function.iterate_succ_apply, hangle, ← add_assoc,
        circleNormal_add_pi_div_two, ih,
        normalizedEuclideanCovector_quarterTurnBasis]

/-- Adjacent chord charts have identical real lifted angles at the common
endpoint, proved from their actual selected support and its positive axis
evaluation. -/
theorem chordSelectedAngle_seam (B : Module.Basis (Fin 2) ℝ E) :
    chordSelectedAngle B 1 = chordSelectedAngle (quarterTurnBasis B) 0 + Real.pi / 2 := by
  have hnorm : chordSelectedSupport B 1 (B 1) = ‖B 1‖ := by
    simpa only [sub_self, zero_smul, one_smul, zero_add] using
      (chordSelectedSupport_mem_normingFunctionals B 1).2
  have hpos : 0 < chordSelectedSupport B 1 (B 1) := by
    rw [hnorm]
    exact norm_pos_iff.mpr (B.ne_zero 1)
  unfold chordSelectedAngle
  rw [← chordSelectedSupport_seam]
  exact (supportAngle_quarterTurnBasis_add_pi_div_two B _ hpos).symm

end Markov
