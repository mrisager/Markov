import Markov.MatrixTraceRay
import Markov.SelectedTraceValue

/-! The algebraic holonomy assignment on the positive Farey sector.
The generators and their descendants are integer matrices. -/

namespace Markov

abbrev IntMatrixTwo := Matrix (Fin 2) (Fin 2) ℤ

/-- The three trace values of an integral matrix pair carry positive Fricke
arithmetic, with the modular divisibility by 3. -/
structure PositiveFrickePair (M N : IntMatrixTwo) : Prop where
  det_left : M.det = 1
  det_right : N.det = 1
  trace_left : 3 ≤ M.trace
  trace_right : 3 ≤ N.trace
  trace_product : 3 ≤ (M * N).trace
  fricke : M.trace ^ 2 + N.trace ^ 2 + (M * N).trace ^ 2 =
    M.trace * N.trace * (M * N).trace
  three_left : 3 ∣ M.trace
  three_right : 3 ∣ N.trace
  three_product : 3 ∣ (M * N).trace

/-- A Fricke root paired with two traces at least 3 is itself at least 3. -/
theorem fricke_third_ge_three (t b c : ℤ) (ht : 3 ≤ t) (hb : 3 ≤ b)
    (hf : t ^ 2 + b ^ 2 + c ^ 2 = t * b * c) : 3 ≤ c := by
  by_contra h
  have hc : c ≤ 2 := by omega
  have hp : 0 ≤ t * b := by positivity
  have hm : t * b * c ≤ 2 * (t * b) := by nlinarith
  have hz : c = 0 := by nlinarith [sq_nonneg (t - b), sq_nonneg c]
  subst c
  nlinarith [sq_nonneg b]

theorem matrix_trace_left_move (M N : IntMatrixTwo) (hM : M.det = 1) :
    (M * (M * N)).trace = M.trace * (M * N).trace - N.trace := by
  simpa only [Nat.zero_add, pow_two, pow_one, pow_zero, one_mul, Matrix.mul_assoc]
    using matrix_trace_ray_recurrence M N hM 0

theorem matrix_trace_right_move (M N : IntMatrixTwo) (hN : N.det = 1) :
    ((M * N) * N).trace = N.trace * (M * N).trace - M.trace := by
  have h := matrix_trace_ray_recurrence N M hN 0
  simp only [Nat.zero_add, pow_two, pow_one, pow_zero, one_mul] at h
  calc
    _ = (M * (N * N)).trace := by rw [Matrix.mul_assoc]
    _ = ((N * N) * M).trace := Matrix.trace_mul_comm _ _
    _ = _ := by rw [h, Matrix.trace_mul_comm N M]

theorem PositiveFrickePair.left {M N : IntMatrixTwo} (h : PositiveFrickePair M N) :
    PositiveFrickePair M (M * N) := by
  have ht := matrix_trace_left_move M N h.det_left
  have hf : M.trace ^ 2 + (M * N).trace ^ 2 + (M * (M * N)).trace ^ 2 =
      M.trace * (M * N).trace * (M * (M * N)).trace := by
    rw [ht]
    nlinarith [h.fricke]
  refine ⟨h.det_left, ?_, h.trace_left, h.trace_product,
    fricke_third_ge_three _ _ _ h.trace_left h.trace_product hf,
    hf, h.three_left, h.three_product, ?_⟩
  · rw [Matrix.det_mul, h.det_left, h.det_right, one_mul]
  · rw [ht]
    exact dvd_sub (dvd_mul_of_dvd_left h.three_left _) h.three_right

theorem PositiveFrickePair.right {M N : IntMatrixTwo} (h : PositiveFrickePair M N) :
    PositiveFrickePair (M * N) N := by
  have ht := matrix_trace_right_move M N h.det_right
  have hf : (M * N).trace ^ 2 + N.trace ^ 2 + ((M * N) * N).trace ^ 2 =
      (M * N).trace * N.trace * ((M * N) * N).trace := by
    rw [ht]
    nlinarith [h.fricke]
  refine ⟨?_, h.det_right, h.trace_product, h.trace_right,
    fricke_third_ge_three _ _ _ h.trace_product h.trace_right hf,
    hf, h.three_product, h.three_right, ?_⟩
  · rw [Matrix.det_mul, h.det_left, h.det_right, one_mul]
  · rw [ht]
    exact dvd_sub (dvd_mul_of_dvd_left h.three_right _) h.three_left

theorem seed_positiveFrickePair : PositiveFrickePair modularGeneratorA modularGeneratorB := by
  rcases modular_generators_det_trace with ⟨hA, hB, htA, htB, htAB⟩
  refine ⟨hA, hB, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [htA, htB, htAB]

/-- Matrix words labelled by the adjacent integral directions of the
positive Farey tree. -/
inductive FareyHolonomy : (ℤ × ℤ) → (ℤ × ℤ) → IntMatrixTwo → IntMatrixTwo → Prop
  | seed : FareyHolonomy (1, 0) (0, 1) modularGeneratorA modularGeneratorB
  | left {u v M N} : FareyHolonomy u v M N → FareyHolonomy u (u + v) M (M * N)
  | right {u v M N} : FareyHolonomy u v M N → FareyHolonomy (u + v) v (M * N) N

/-- Every constructed Farey pair supplies integer traces at least 3,
the Fricke relation, and the modular divisibility. -/
theorem FareyHolonomy.positiveFrickePair {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : FareyHolonomy u v M N) : PositiveFrickePair M N := by
  induction h with
  | seed => exact seed_positiveFrickePair
  | left _ ih => exact ih.left
  | right _ ih => exact ih.right

/-- The direction labels remain unimodular throughout the concrete tree. -/
theorem FareyHolonomy.det_eq_one {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : FareyHolonomy u v M N) : intDet u v = 1 := by
  induction h with
  | seed => norm_num [intDet]
  | @left u v M N _ ih =>
    simp only [intDet, Prod.fst_add, Prod.snd_add] at *
    nlinarith
  | @right u v M N _ ih =>
    simp only [intDet, Prod.fst_add, Prod.snd_add] at *
    nlinarith

/-- Every generated matrix pair retains the puncture trace condition. -/
theorem FareyHolonomy.commutator_trace {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : FareyHolonomy u v M N) : (M * N * M.adjugate * N.adjugate).trace = -2 := by
  have hp := h.positiveFrickePair
  have hf := matrix_fricke_polynomial M N
  rw [hp.det_left, hp.det_right] at hf
  linarith [hp.fricke]

/-- The labelled directions are primitive, in the Bezout sense. -/
theorem FareyHolonomy.primitive_labels {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : FareyHolonomy u v M N) : IsCoprime u.1 u.2 ∧ IsCoprime v.1 v.2 := by
  have hd := h.det_eq_one
  dsimp [intDet] at hd
  constructor
  · exact ⟨v.2, -v.1, by nlinarith⟩
  · exact ⟨-u.2, u.1, by nlinarith⟩

/-- Division of the actual traces by 3 produces positive integral Markov
solutions. No ordering or global orbit correspondence is asserted here. -/
theorem PositiveFrickePair.markovTriple {M N : IntMatrixTwo} (h : PositiveFrickePair M N) :
    ∃ a b c : ℤ, M.trace = 3 * a ∧ N.trace = 3 * b ∧ (M * N).trace = 3 * c ∧
      1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧ a ^ 2 + b ^ 2 + c ^ 2 = 3 * a * b * c := by
  obtain ⟨a, ha⟩ := h.three_left
  obtain ⟨b, hb⟩ := h.three_right
  obtain ⟨c, hc⟩ := h.three_product
  refine ⟨a, b, c, ha, hb, hc, ?_, ?_, ?_, ?_⟩
  · linarith [h.trace_left]
  · linarith [h.trace_right]
  · linarith [h.trace_product]
  · have hf := h.fricke
    rw [ha, hb, hc] at hf
    nlinarith

/-- Repeated Farey moves identify the integral direction with the actual
matrix word, rather than merely matching its numerical trace recurrence. -/
theorem FareyHolonomy.integral_ray {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : FareyHolonomy u v M N) (n : ℕ) :
    FareyHolonomy u (n • u + v) M (M ^ n * N) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    have hv : (n + 1) • u + v = u + (n • u + v) := by
      rw [add_nsmul, one_nsmul]
      abel
    rw [hv, pow_succ', Matrix.mul_assoc]
    exact ih.left

/-- The primitive direction along the ray and its matrix word both occur in
the concrete construction. -/
theorem FareyHolonomy.integral_ray_primitive {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : FareyHolonomy u v M N) (n : ℕ) :
    IsCoprime (n • u + v).1 (n • u + v).2 :=
  (h.integral_ray n).primitive_labels.2

/-- Every concrete Farey pair satisfies the separation estimate once the
norm/trace length relation is supplied. All arithmetic, primitivity, matrix
recurrence, and selected-value inputs are derived from the construction. -/
theorem FareyHolonomy.separation_of_trace_lengths
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : Module.Basis (Fin 2) ℝ E) {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : FareyHolonomy u v M N) (d : ℤ × ℤ) (A : ℝ)
    (hA : 1 ≤ A) (hu : intHeight u ≤ A) (hv : intHeight v ≤ 2 * A)
    (hd : d ≠ (0, 0))
    (htu : (M.trace : ℝ) = 2 * Real.cosh (‖intVector B u‖ / 2))
    (hbv : (N.trace : ℝ) = 2 * Real.cosh (‖intVector B v‖ / 2))
    (hray : ∀ n : ℕ, ((M ^ (n + 1) * N).trace : ℝ) =
      2 * Real.cosh (‖((n : ℝ) + 1) • intVector B u + intVector B v‖ / 2)) :
    Real.exp (-(planeSeparationConstant B * intEuclidean d * A ^ 2)) ≤
      |integralCovectorDet (dualCoordinates B (selectedSupportAt B u v)) d| := by
  have hp := h.positiveFrickePair
  letI : Fact (3 ≤ M.trace) := ⟨hp.trace_left⟩
  exact selectedSupport_det_lower_bound_of_matrix_traces B M N (by linarith [hp.trace_right])
    hp.det_left hp.det_right h.commutator_trace u v d A hA hu hv
    (by rw [h.det_eq_one]; norm_num) hd htu hbv hray

/-- The remaining geometric property of a norm, stated explicitly. This is
not an axiom or an assertion that such a norm has been constructed. -/
def FareyTraceLengthCompatible {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : Module.Basis (Fin 2) ℝ E) : Prop :=
  ∀ {u v : ℤ × ℤ} {M N : IntMatrixTwo}, FareyHolonomy u v M N →
    (M.trace : ℝ) = 2 * Real.cosh (‖intVector B u‖ / 2) ∧
    (N.trace : ℝ) = 2 * Real.cosh (‖intVector B v‖ / 2)

theorem intVector_nsmul_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : Module.Basis (Fin 2) ℝ E) (u v : ℤ × ℤ) (n : ℕ) :
    intVector B (n • u + v) = (n : ℝ) • intVector B u + intVector B v := by
  simp [intVector, nsmul_eq_mul, smul_add, add_smul, smul_smul]
  module

/-- Relative separation on the concrete Farey tree: the single norm/trace
compatibility hypothesis supplies all ray lengths through the checked moves. -/
theorem FareyHolonomy.separation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : Module.Basis (Fin 2) ℝ E) (htrace : FareyTraceLengthCompatible B)
    {u v : ℤ × ℤ} {M N : IntMatrixTwo} (h : FareyHolonomy u v M N)
    (d : ℤ × ℤ) (A : ℝ) (hA : 1 ≤ A) (hu : intHeight u ≤ A)
    (hv : intHeight v ≤ 2 * A) (hd : d ≠ (0, 0)) :
    Real.exp (-(planeSeparationConstant B * intEuclidean d * A ^ 2)) ≤
      |integralCovectorDet (dualCoordinates B (selectedSupportAt B u v)) d| := by
  apply h.separation_of_trace_lengths B d A hA hu hv hd (htrace h).1 (htrace h).2
  intro n
  have hr := (htrace (h.integral_ray (n + 1))).2
  simpa only [intVector_nsmul_add, Nat.cast_add, Nat.cast_one] using hr

end Markov
