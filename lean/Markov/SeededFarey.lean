import Markov.FareyCoverage

/-! Farey words with an arbitrary initial direction basis and integral
matrix pair. This transports the checked positive-sector construction to
other lattice cones; geometric trace–length compatibility is not asserted. -/

namespace Markov

/-- Integral coordinates relative to a chosen pair of direction vectors. -/
def seededDirection (u0 v0 a : ℤ × ℤ) : ℤ × ℤ := a.1 • u0 + a.2 • v0

theorem seededDirection_zero_one (u0 v0 : ℤ × ℤ) :
    seededDirection u0 v0 (1, 0) = u0 ∧ seededDirection u0 v0 (0, 1) = v0 := by
  simp [seededDirection]

theorem seededDirection_add (u0 v0 a b : ℤ × ℤ) :
    seededDirection u0 v0 (a + b) = seededDirection u0 v0 a + seededDirection u0 v0 b := by
  dsimp [seededDirection]
  module

theorem seededDirection_det (u0 v0 a b : ℤ × ℤ) :
    intDet (seededDirection u0 v0 a) (seededDirection u0 v0 b) =
      intDet a b * intDet u0 v0 := by
  simp [intDet, seededDirection, zsmul_eq_mul]
  ring

/-- The same two Farey moves starting from arbitrary direction and matrix
seeds. Matrices and directions are transformed along the same word path. -/
inductive SeededFarey (u0 v0 : ℤ × ℤ) (M0 N0 : IntMatrixTwo) :
    (ℤ × ℤ) → (ℤ × ℤ) → IntMatrixTwo → IntMatrixTwo → Prop
  | seed : SeededFarey u0 v0 M0 N0 u0 v0 M0 N0
  | left {u v M N} : SeededFarey u0 v0 M0 N0 u v M N →
      SeededFarey u0 v0 M0 N0 u (u + v) M (M * N)
  | right {u v M N} : SeededFarey u0 v0 M0 N0 u v M N →
      SeededFarey u0 v0 M0 N0 (u + v) v (M * N) N

/-- Positivity, determinant, Fricke and divisibility properties propagate
from an arbitrary arithmetic seed along the actual matrix moves. -/
theorem SeededFarey.positiveFrickePair {u0 v0 u v : ℤ × ℤ} {M0 N0 M N : IntMatrixTwo}
    (hp : PositiveFrickePair M0 N0) (h : SeededFarey u0 v0 M0 N0 u v M N) :
    PositiveFrickePair M N := by
  induction h with
  | seed => exact hp
  | left _ ih => exact ih.left
  | right _ ih => exact ih.right

/-- The direction determinant is preserved even before imposing a
unimodularity condition on the seed. -/
theorem SeededFarey.det_eq_seed {u0 v0 u v : ℤ × ℤ} {M0 N0 M N : IntMatrixTwo}
    (h : SeededFarey u0 v0 M0 N0 u v M N) : intDet u v = intDet u0 v0 := by
  induction h with
  | seed => rfl
  | @left u v M N _ ih =>
    simp only [intDet, Prod.fst_add, Prod.snd_add] at *
    nlinarith
  | @right u v M N _ ih =>
    simp only [intDet, Prod.fst_add, Prod.snd_add] at *
    nlinarith

/-- Replace the standard seed by any chosen direction and matrix pair,
retaining the same Farey word path. -/
theorem FareyHolonomy.to_seeded {a b : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : FareyHolonomy a b M N) (u0 v0 : ℤ × ℤ) (M0 N0 : IntMatrixTwo) :
    ∃ P Q, SeededFarey u0 v0 M0 N0 (seededDirection u0 v0 a)
      (seededDirection u0 v0 b) P Q := by
  induction h with
  | seed =>
    refine ⟨M0, N0, ?_⟩
    simpa only [(seededDirection_zero_one u0 v0).1, (seededDirection_zero_one u0 v0).2]
      using (SeededFarey.seed (u0 := u0) (v0 := v0) (M0 := M0) (N0 := N0))
  | left _ ih =>
    obtain ⟨P, Q, hh⟩ := ih
    refine ⟨P, P * Q, ?_⟩
    simpa only [seededDirection_add] using hh.left
  | right _ ih =>
    obtain ⟨P, Q, hh⟩ := ih
    refine ⟨P * Q, Q, ?_⟩
    simpa only [seededDirection_add] using hh.right

/-- Coverage of every nonnegative unimodular coordinate pair in an
arbitrary seeded lattice cone. No geometric interpretation is required. -/
theorem exists_seededFarey_of_nonnegative_coordinates
    (u0 v0 a b : ℤ × ℤ) (M0 N0 : IntMatrixTwo)
    (ha1 : 0 ≤ a.1) (ha2 : 0 ≤ a.2) (hb1 : 0 ≤ b.1) (hb2 : 0 ≤ b.2)
    (hd : intDet a b = 1) :
    ∃ P Q, SeededFarey u0 v0 M0 N0 (seededDirection u0 v0 a)
      (seededDirection u0 v0 b) P Q := by
  obtain ⟨M, N, h⟩ := exists_fareyHolonomy_of_nonnegative a b ha1 ha2 hb1 hb2 hd
  exact h.to_seeded u0 v0 M0 N0

/-- Integral rays remain in the same seeded cone with the exact matrix word. -/
theorem SeededFarey.integral_ray {u0 v0 u v : ℤ × ℤ} {M0 N0 M N : IntMatrixTwo}
    (h : SeededFarey u0 v0 M0 N0 u v M N) (n : ℕ) :
    SeededFarey u0 v0 M0 N0 u (n • u + v) M (M ^ n * N) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    have hv : (n + 1) • u + v = u + (n • u + v) := by
      rw [add_nsmul, one_nsmul]
      abel
    rw [hv, pow_succ', Matrix.mul_assoc]
    exact ih.left

/-- The commutator trace condition follows from propagated Fricke arithmetic. -/
theorem SeededFarey.commutator_trace {u0 v0 u v : ℤ × ℤ} {M0 N0 M N : IntMatrixTwo}
    (hp : PositiveFrickePair M0 N0) (h : SeededFarey u0 v0 M0 N0 u v M N) :
    (M * N * M.adjugate * N.adjugate).trace = -2 := by
  have hh := h.positiveFrickePair hp
  have hf := matrix_fricke_polynomial M N
  rw [hh.det_left, hh.det_right] at hf
  linarith [hh.fricke]

/-- Repeated right moves give the other integral ray with its exact word. -/
theorem SeededFarey.right_integral_ray {u0 v0 u v : ℤ × ℤ} {M0 N0 M N : IntMatrixTwo}
    (h : SeededFarey u0 v0 M0 N0 u v M N) (n : ℕ) :
    SeededFarey u0 v0 M0 N0 (u + n • v) v (M * N ^ n) N := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    have hu : u + (n + 1) • v = (u + n • v) + v := by
      rw [add_nsmul, one_nsmul]
      abel
    rw [hu, pow_succ, ← Matrix.mul_assoc]
    exact ih.right

end Markov
