import Markov.FareyConsistency
import Markov.PrimitivePartner

/-! Canonical matrices, traces and numerical lengths on primitive
nonnegative directions. The matrix assignment is independent of the partner
and the side of the Farey edge. `IntrinsicMcShaneRivinNorm` relates the
constructed trace norm to the geometric norm. -/

noncomputable section

namespace Markov

/-- Primitive integral directions in the closed nonnegative quadrant. -/
def NonnegativePrimitiveDirection (p : ℤ × ℤ) : Prop :=
  0 ≤ p.1 ∧ 0 ≤ p.2 ∧ IsCoprime p.1 p.2

/-- An actual matrix carried by the direction, on either side of an edge. -/
def CarriesFareyMatrix (p : ℤ × ℤ) (M : IntMatrixTwo) : Prop :=
  (∃ v N, FareyHolonomy p v M N) ∨ (∃ u N, FareyHolonomy u p N M)

/-- Partner choice and edge side do not change a direction's matrix. -/
theorem carriesFareyMatrix_unique {p : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : CarriesFareyMatrix p M) (h' : CarriesFareyMatrix p N) : M = N := by
  rcases h with ⟨v, Q, h⟩ | ⟨u, P, h⟩
  · rcases h' with ⟨w, R, h'⟩ | ⟨w, R, h'⟩
    · exact h.first_matrix_unique h'
    · exact h.cross_matrix_unique h'
  · rcases h' with ⟨w, R, h'⟩ | ⟨w, R, h'⟩
    · exact (h'.cross_matrix_unique h).symm
    · exact h.second_matrix_unique h'

/-- Every primitive direction in this sector carries an actual matrix. -/
theorem exists_carriesFareyMatrix (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) :
    ∃ M, CarriesFareyMatrix p M := by
  obtain ⟨u, v, hu1, hu2, hv1, hv2, hd, he⟩ :=
    nonnegative_primitive_in_unimodular_pair p hp.1 hp.2.1 hp.2.2
  obtain ⟨M, N, h⟩ := exists_fareyHolonomy_of_nonnegative u v hu1 hu2 hv1 hv2 hd
  rcases he with rfl | rfl
  · exact ⟨M, Or.inl ⟨v, N, h⟩⟩
  · exact ⟨N, Or.inr ⟨u, M, h⟩⟩

theorem exists_unique_carriesFareyMatrix (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) :
    ∃! M, CarriesFareyMatrix p M := by
  obtain ⟨M, hM⟩ := exists_carriesFareyMatrix p hp
  exact ⟨M, hM, fun N hN => carriesFareyMatrix_unique hN hM⟩

/-- The canonical matrix of a primitive nonnegative direction. -/
def primitiveFareyMatrix (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) : IntMatrixTwo :=
  Classical.choose (exists_carriesFareyMatrix p hp)

theorem primitiveFareyMatrix_spec (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) :
    CarriesFareyMatrix p (primitiveFareyMatrix p hp) :=
  Classical.choose_spec (exists_carriesFareyMatrix p hp)

theorem primitiveFareyMatrix_eq_of_carries {p : ℤ × ℤ} (hp : NonnegativePrimitiveDirection p)
    {M : IntMatrixTwo} (h : CarriesFareyMatrix p M) : primitiveFareyMatrix p hp = M :=
  carriesFareyMatrix_unique (primitiveFareyMatrix_spec p hp) h

theorem primitiveFareyMatrix_det (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) :
    (primitiveFareyMatrix p hp).det = 1 := by
  rcases primitiveFareyMatrix_spec p hp with ⟨v, N, h⟩ | ⟨u, N, h⟩
  · exact h.positiveFrickePair.det_left
  · exact h.positiveFrickePair.det_right

/-- The canonical integer trace. -/
def primitiveFareyTrace (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) : ℤ :=
  (primitiveFareyMatrix p hp).trace

theorem primitiveFareyTrace_ge_three (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) :
    3 ≤ primitiveFareyTrace p hp := by
  rcases primitiveFareyMatrix_spec p hp with ⟨v, N, h⟩ | ⟨u, N, h⟩
  · exact h.positiveFrickePair.trace_left
  · exact h.positiveFrickePair.trace_right

theorem primitiveFareyTrace_dvd_three (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) :
    3 ∣ primitiveFareyTrace p hp := by
  rcases primitiveFareyMatrix_spec p hp with ⟨v, N, h⟩ | ⟨u, N, h⟩
  · exact h.positiveFrickePair.three_left
  · exact h.positiveFrickePair.three_right

/-- The numerical trace-length assignment on primitive directions. -/
def primitiveFareyLength (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) : ℝ :=
  2 * Real.arcosh ((primitiveFareyTrace p hp : ℝ) / 2)

theorem primitiveFareyLength_pos (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) :
    0 < primitiveFareyLength p hp := by
  have ht : (3 : ℝ) ≤ primitiveFareyTrace p hp := by
    exact_mod_cast primitiveFareyTrace_ge_three p hp
  exact mul_pos (by norm_num) (Real.arcosh_pos (by linarith))

/-- The candidate lengths have the required numerical trace–length relation
by their definition. No norm/geodesic interpretation is used here. -/
theorem primitiveFareyTrace_eq_two_cosh (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) :
    (primitiveFareyTrace p hp : ℝ) = 2 * Real.cosh (primitiveFareyLength p hp / 2) := by
  have ht : (3 : ℝ) ≤ primitiveFareyTrace p hp := by
    exact_mod_cast primitiveFareyTrace_ge_three p hp
  have hh : primitiveFareyLength p hp / 2 =
      Real.arcosh ((primitiveFareyTrace p hp : ℝ) / 2) := by
    dsimp [primitiveFareyLength]
    ring
  rw [hh, Real.cosh_arcosh (by linarith)]
  ring

theorem FareyHolonomy.left_nonnegativePrimitive {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : FareyHolonomy u v M N) : NonnegativePrimitiveDirection u :=
  ⟨h.nonnegative_labels.1, h.nonnegative_labels.2.1, h.primitive_labels.1⟩

theorem FareyHolonomy.right_nonnegativePrimitive {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : FareyHolonomy u v M N) : NonnegativePrimitiveDirection v :=
  ⟨h.nonnegative_labels.2.2.1, h.nonnegative_labels.2.2.2, h.primitive_labels.2⟩

/-- Identifying the canonical matrices with either matrix of a Farey pair. -/
theorem FareyHolonomy.primitiveFareyMatrix_left {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : FareyHolonomy u v M N) (hu : NonnegativePrimitiveDirection u) :
    primitiveFareyMatrix u hu = M :=
  primitiveFareyMatrix_eq_of_carries hu (Or.inl ⟨v, N, h⟩)

theorem FareyHolonomy.primitiveFareyMatrix_right {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : FareyHolonomy u v M N) (hv : NonnegativePrimitiveDirection v) :
    primitiveFareyMatrix v hv = N :=
  primitiveFareyMatrix_eq_of_carries hv (Or.inr ⟨u, M, h⟩)

/-- A norm with the prescribed primitive lengths satisfies trace compatibility. -/
theorem fareyTraceLengthCompatible_of_primitive_lengths
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : Module.Basis (Fin 2) ℝ E)
    (hL : ∀ p : ℤ × ℤ, ∀ hp : NonnegativePrimitiveDirection p,
      ‖intVector B p‖ = primitiveFareyLength p hp) : FareyTraceLengthCompatible B := by
  intro u v M N h
  have hu := primitiveFareyTrace_eq_two_cosh u h.left_nonnegativePrimitive
  have hv := primitiveFareyTrace_eq_two_cosh v h.right_nonnegativePrimitive
  simp only [primitiveFareyTrace, h.primitiveFareyMatrix_left, h.primitiveFareyMatrix_right] at hu hv
  rw [← hL u h.left_nonnegativePrimitive] at hu
  rw [← hL v h.right_nonnegativePrimitive] at hv
  exact ⟨hu, hv⟩

/-- Canonical traces obey the Fricke equation on each Farey triangle. -/
theorem FareyHolonomy.canonicalTrace_fricke {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : FareyHolonomy u v M N) (hu : NonnegativePrimitiveDirection u)
    (hv : NonnegativePrimitiveDirection v) (hs : NonnegativePrimitiveDirection (u + v)) :
    primitiveFareyTrace u hu ^ 2 + primitiveFareyTrace v hv ^ 2 +
      primitiveFareyTrace (u + v) hs ^ 2 =
      primitiveFareyTrace u hu * primitiveFareyTrace v hv * primitiveFareyTrace (u + v) hs := by
  simp only [primitiveFareyTrace, h.primitiveFareyMatrix_left, h.primitiveFareyMatrix_right,
    h.left.primitiveFareyMatrix_right]
  exact h.positiveFrickePair.fricke

/-- The canonical candidate function follows the actual matrix words along
integral rays; this is no longer an assumed choice of partners. -/
theorem FareyHolonomy.canonicalMatrix_integral_ray {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : FareyHolonomy u v M N) (n : ℕ) (hp : NonnegativePrimitiveDirection (n • u + v)) :
    primitiveFareyMatrix (n • u + v) hp = M ^ n * N :=
  (h.integral_ray n).primitiveFareyMatrix_right hp

theorem FareyHolonomy.canonicalTrace_integral_ray {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : FareyHolonomy u v M N) (n : ℕ) (hp : NonnegativePrimitiveDirection (n • u + v)) :
    primitiveFareyTrace (n • u + v) hp = (M ^ n * N).trace := by
  rw [primitiveFareyTrace, h.canonicalMatrix_integral_ray n hp]

end Markov
