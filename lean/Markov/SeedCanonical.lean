import Markov.SeededFarey
import Markov.FareyConsistency
import Markov.CanonicalTrace
import Markov.FrickeLengthTriangle

/-! Canonical primitive matrix words for any initial integral matrix seed.
Consistency is proved independently of matrix arithmetic; positivity and
Fricke properties are later supplied by PositiveFrickePair on the seed. -/

noncomputable section
namespace Markov

variable {M0 N0 : IntMatrixTwo}

theorem SeededFarey.coordinate_nonnegative_labels {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (1, 0) (0, 1) M0 N0 u v M N) :
    0 ≤ u.1 ∧ 0 ≤ u.2 ∧ 0 ≤ v.1 ∧ 0 ≤ v.2 := by
  induction h with
  | seed => norm_num
  | left _ ih => rcases ih with ⟨h1,h2,h3,h4⟩; exact ⟨h1,h2,add_nonneg h1 h3,add_nonneg h2 h4⟩
  | right _ ih => rcases ih with ⟨h1,h2,h3,h4⟩; exact ⟨add_nonneg h1 h3,add_nonneg h2 h4,h3,h4⟩

theorem SeededFarey.coordinate_det_eq_one {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (1, 0) (0, 1) M0 N0 u v M N) : intDet u v = 1 := by
  simpa [intDet] using h.det_eq_seed

theorem SeededFarey.coordinate_primitive_labels {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (1, 0) (0, 1) M0 N0 u v M N) : IsCoprime u.1 u.2 ∧ IsCoprime v.1 v.2 := by
  have hd := h.coordinate_det_eq_one
  dsimp [intDet] at hd
  exact ⟨⟨v.2, -v.1, by nlinarith⟩, ⟨-u.2, u.1, by nlinarith⟩⟩

theorem SeededFarey.coordinate_nonzero_labels {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (1, 0) (0, 1) M0 N0 u v M N) : u ≠ 0 ∧ v ≠ 0 := by
  have hd := h.coordinate_det_eq_one
  constructor <;> intro hz <;> simp [hz, intDet] at hd


theorem SeededFarey.coordinate_matrices_unique_general {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (1, 0) (0, 1) M0 N0 u v M N) :
    ∀ {u' v' : ℤ × ℤ} {M' N' : IntMatrixTwo}, SeededFarey (1, 0) (0, 1) M0 N0 u' v' M' N' →
      u = u' → v = v' → M = M' ∧ N = N' := by
  induction h with
  | seed =>
    intro u' v' M' N' h' he he'
    cases h' with
    | seed => exact ⟨rfl, rfl⟩
    | @left a b P Q hp =>
      exact False.elim (nonnegative_not_left_seed _ _ hp.coordinate_nonnegative_labels.2.2.1 he.symm he'.symm)
    | @right a b P Q hp =>
      exact False.elim (nonnegative_not_right_seed _ _ hp.coordinate_nonnegative_labels.2.1 he.symm he'.symm)
  | @left u v M N hp ih =>
    intro u' v' M' N' h' he he'
    cases h' with
    | seed =>
      exact False.elim (nonnegative_not_left_seed u v hp.coordinate_nonnegative_labels.2.2.1 he he')
    | @left a b P Q hq =>
      rcases ih hq he (by rw [he] at he'; exact add_left_cancel he') with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
    | @right a b P Q hq =>
      exact False.elim (nonnegative_left_right_disjoint _ _ _ _
        hp.coordinate_nonnegative_labels.2.2.1 hp.coordinate_nonnegative_labels.2.2.2
        hq.coordinate_nonnegative_labels.1 hq.coordinate_nonnegative_labels.2.1 hp.coordinate_nonzero_labels.2 he he')
  | @right u v M N hp ih =>
    intro u' v' M' N' h' he he'
    cases h' with
    | seed =>
      exact False.elim (nonnegative_not_right_seed u v hp.coordinate_nonnegative_labels.2.1 he he')
    | @left a b P Q hq =>
      exact False.elim (nonnegative_left_right_disjoint _ _ _ _
        hq.coordinate_nonnegative_labels.2.2.1 hq.coordinate_nonnegative_labels.2.2.2
        hp.coordinate_nonnegative_labels.1 hp.coordinate_nonnegative_labels.2.1 hq.coordinate_nonzero_labels.2 he.symm he'.symm)
    | @right a b P Q hq =>
      rcases ih hq (by rw [he'] at he; exact add_right_cancel he) he' with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩


theorem SeededFarey.coordinate_matrices_unique {u v : ℤ × ℤ} {M N M' N' : IntMatrixTwo}
    (h : SeededFarey (1, 0) (0, 1) M0 N0 u v M N) (h' : SeededFarey (1, 0) (0, 1) M0 N0 u v M' N') : M = M' ∧ N = N' :=
  h.coordinate_matrices_unique_general h' rfl rfl


theorem SeededFarey.coordinate_first_matrix_unique {u v w : ℤ × ℤ} {M N P Q : IntMatrixTwo}
    (h : SeededFarey (1, 0) (0, 1) M0 N0 u v M N) (h' : SeededFarey (1, 0) (0, 1) M0 N0 u w P Q) : M = P := by
  obtain ⟨k, he⟩ := unimodular_partners_exists_shear u v w h.coordinate_det_eq_one h'.coordinate_det_eq_one
  by_cases hk : 0 ≤ k
  · have hv : k.toNat • u + w = v := by
      rw [toNat_nsmul_eq_zsmul k hk]
      rw [he, add_comm]
    have hr := h'.integral_ray k.toNat
    rw [hv] at hr
    exact (h.coordinate_matrices_unique hr).1
  · have hneg : 0 ≤ -k := by omega
    have hw : (-k).toNat • u + v = w := by
      rw [toNat_nsmul_eq_zsmul (-k) hneg, he, neg_smul]
      abel
    have hr := h.integral_ray (-k).toNat
    rw [hw] at hr
    exact (hr.coordinate_matrices_unique h').1


theorem SeededFarey.coordinate_second_matrix_unique {u v w : ℤ × ℤ} {M N P Q : IntMatrixTwo}
    (h : SeededFarey (1, 0) (0, 1) M0 N0 u v M N) (h' : SeededFarey (1, 0) (0, 1) M0 N0 w v P Q) : N = Q := by
  have hvu : intDet v u = -1 := by
    have hh := h.coordinate_det_eq_one
    dsimp [intDet] at *
    linarith
  have hvw : intDet v w = -1 := by
    have hh := h'.coordinate_det_eq_one
    dsimp [intDet] at *
    linarith
  obtain ⟨k, he⟩ := neg_unimodular_partners_exists_shear v u w hvu hvw
  by_cases hk : 0 ≤ k
  · have hu : w + k.toNat • v = u := by
      rw [toNat_nsmul_eq_zsmul k hk, he]
    have hr := h'.right_integral_ray k.toNat
    rw [hu] at hr
    exact (h.coordinate_matrices_unique hr).2
  · have hneg : 0 ≤ -k := by omega
    have hw : u + (-k).toNat • v = w := by
      rw [toNat_nsmul_eq_zsmul (-k) hneg, he, neg_smul]
      abel
    have hr := h.right_integral_ray (-k).toNat
    rw [hw] at hr
    exact (hr.coordinate_matrices_unique h').2


theorem SeededFarey.coordinate_positive_mass {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (1, 0) (0, 1) M0 N0 u v M N) : 0 < u.1 + u.2 ∧ 0 < v.1 + v.2 := by
  rcases h.coordinate_nonnegative_labels with ⟨hu1, hu2, hv1, hv2⟩
  have hd := h.coordinate_det_eq_one
  dsimp [intDet] at hd
  constructor
  · by_contra hn
    have hz1 : u.1 = 0 := by omega
    have hz2 : u.2 = 0 := by omega
    simp [hz1, hz2] at hd
  · by_contra hn
    have hz1 : v.1 = 0 := by omega
    have hz2 : v.2 = 0 := by omega
    simp [hz1, hz2] at hd


theorem SeededFarey.coordinate_cross_matrix_unique_general {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (1, 0) (0, 1) M0 N0 u v M N) :
    ∀ {a b : ℤ × ℤ} {P Q : IntMatrixTwo}, SeededFarey (1, 0) (0, 1) M0 N0 a b P Q → u = b → M = Q := by
  induction h with
  | seed =>
    intro a b P Q h' he
    have hd := h'.coordinate_det_eq_one
    rw [← he] at hd
    have ha := h'.coordinate_nonnegative_labels.2.1
    simp [intDet] at hd
    omega
  | left hp ih =>
    intro a b P Q h' he
    exact ih h' he
  | @right u v M N hp _ =>
    intro a b P Q h' he
    revert he
    induction h' with
    | seed =>
      intro he
      have h1 := congrArg Prod.fst he
      have h2 := congrArg Prod.snd he
      simp at h1 h2
      rcases hp.coordinate_positive_mass with ⟨hu, hv⟩
      omega
    | left hq _ =>
      intro he
      have hs := unimodular_positive_sum_unique _ _ _ _ hp.coordinate_positive_mass.1 hp.coordinate_positive_mass.2
        hq.coordinate_positive_mass.1 hq.coordinate_positive_mass.2 hp.coordinate_det_eq_one hq.coordinate_det_eq_one he
      rcases hp.coordinate_matrices_unique_general hq hs.1 hs.2 with ⟨hm, hn⟩
      rw [hm, hn]
    | right hq ih =>
      intro he
      exact ih he


theorem SeededFarey.coordinate_cross_matrix_unique {u v w : ℤ × ℤ} {M N P Q : IntMatrixTwo}
    (h : SeededFarey (1, 0) (0, 1) M0 N0 u v M N) (h' : SeededFarey (1, 0) (0, 1) M0 N0 w u P Q) : M = Q :=
  h.coordinate_cross_matrix_unique_general h' rfl


/-- Coverage of every nonnegative unimodular coordinate pair for any matrix seed. -/
theorem exists_coordinateSeededFarey_of_nonnegative (M0 N0 : IntMatrixTwo)
    (u v : ℤ × ℤ) (hu1 : 0 ≤ u.1) (hu2 : 0 ≤ u.2) (hv1 : 0 ≤ v.1) (hv2 : 0 ≤ v.2)
    (hd : intDet u v = 1) : ∃ M N, SeededFarey (1, 0) (0, 1) M0 N0 u v M N := by
  obtain ⟨M, N, h⟩ := exists_seededFarey_of_nonnegative_coordinates
    (1, 0) (0, 1) u v M0 N0 hu1 hu2 hv1 hv2 hd
  exact ⟨M, N, by simpa [seededDirection, zsmul_eq_mul] using h⟩

def CarriesSeedMatrix (M0 N0 : IntMatrixTwo) (p : ℤ × ℤ) (M : IntMatrixTwo) : Prop :=
  (∃ v N, SeededFarey (1, 0) (0, 1) M0 N0 p v M N) ∨
    (∃ u N, SeededFarey (1, 0) (0, 1) M0 N0 u p N M)

theorem carriesSeedMatrix_unique {p : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : CarriesSeedMatrix M0 N0 p M) (h' : CarriesSeedMatrix M0 N0 p N) : M = N := by
  rcases h with ⟨v, Q, h⟩ | ⟨u, P, h⟩
  · rcases h' with ⟨w, R, h'⟩ | ⟨w, R, h'⟩
    · exact h.coordinate_first_matrix_unique h'
    · exact h.coordinate_cross_matrix_unique h'
  · rcases h' with ⟨w, R, h'⟩ | ⟨w, R, h'⟩
    · exact (h'.coordinate_cross_matrix_unique h).symm
    · exact h.coordinate_second_matrix_unique h'

theorem exists_carriesSeedMatrix (M0 N0 : IntMatrixTwo) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection p) : ∃ M, CarriesSeedMatrix M0 N0 p M := by
  obtain ⟨u, v, hu1, hu2, hv1, hv2, hd, he⟩ :=
    nonnegative_primitive_in_unimodular_pair p hp.1 hp.2.1 hp.2.2
  obtain ⟨M, N, h⟩ := exists_coordinateSeededFarey_of_nonnegative M0 N0 u v hu1 hu2 hv1 hv2 hd
  rcases he with rfl | rfl
  · exact ⟨M, Or.inl ⟨v, N, h⟩⟩
  · exact ⟨N, Or.inr ⟨u, M, h⟩⟩

theorem exists_unique_carriesSeedMatrix (M0 N0 : IntMatrixTwo) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection p) : ∃! M, CarriesSeedMatrix M0 N0 p M := by
  obtain ⟨M, hM⟩ := exists_carriesSeedMatrix M0 N0 p hp
  exact ⟨M, hM, fun N hN => carriesSeedMatrix_unique hN hM⟩

def primitiveSeedMatrix (M0 N0 : IntMatrixTwo) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection p) : IntMatrixTwo :=
  Classical.choose (exists_carriesSeedMatrix M0 N0 p hp)

theorem primitiveSeedMatrix_spec (M0 N0 : IntMatrixTwo) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection p) :
    CarriesSeedMatrix M0 N0 p (primitiveSeedMatrix M0 N0 p hp) :=
  Classical.choose_spec (exists_carriesSeedMatrix M0 N0 p hp)

theorem primitiveSeedMatrix_eq_of_carries {p : ℤ × ℤ} (hp : NonnegativePrimitiveDirection p)
    {M : IntMatrixTwo} (h : CarriesSeedMatrix M0 N0 p M) : primitiveSeedMatrix M0 N0 p hp = M :=
  carriesSeedMatrix_unique (primitiveSeedMatrix_spec M0 N0 p hp) h

def primitiveSeedTrace (M0 N0 : IntMatrixTwo) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection p) : ℤ := (primitiveSeedMatrix M0 N0 p hp).trace

def primitiveSeedLength (M0 N0 : IntMatrixTwo) (p : ℤ × ℤ)
    (hp : NonnegativePrimitiveDirection p) : ℝ :=
  2 * Real.arcosh ((primitiveSeedTrace M0 N0 p hp : ℝ) / 2)

theorem primitiveSeedMatrix_det (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0)
    (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) :
    (primitiveSeedMatrix M0 N0 p hp).det = 1 := by
  rcases primitiveSeedMatrix_spec M0 N0 p hp with ⟨v, N, h⟩ | ⟨u, N, h⟩
  · exact (h.positiveFrickePair h0).det_left
  · exact (h.positiveFrickePair h0).det_right

theorem primitiveSeedTrace_ge_three (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0)
    (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) : 3 ≤ primitiveSeedTrace M0 N0 p hp := by
  rcases primitiveSeedMatrix_spec M0 N0 p hp with ⟨v, N, h⟩ | ⟨u, N, h⟩
  · exact (h.positiveFrickePair h0).trace_left
  · exact (h.positiveFrickePair h0).trace_right

theorem primitiveSeedTrace_three_dvd (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0)
    (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) : 3 ∣ primitiveSeedTrace M0 N0 p hp := by
  rcases primitiveSeedMatrix_spec M0 N0 p hp with ⟨v, N, h⟩ | ⟨u, N, h⟩
  · exact (h.positiveFrickePair h0).three_left
  · exact (h.positiveFrickePair h0).three_right

theorem primitiveSeedLength_pos (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0)
    (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) : 0 < primitiveSeedLength M0 N0 p hp := by
  have ht : (3 : ℝ) ≤ primitiveSeedTrace M0 N0 p hp := by
    exact_mod_cast primitiveSeedTrace_ge_three M0 N0 h0 p hp
  exact mul_pos (by norm_num) (Real.arcosh_pos (by linarith))

theorem primitiveSeedTrace_eq_two_cosh (M0 N0 : IntMatrixTwo) (h0 : PositiveFrickePair M0 N0)
    (p : ℤ × ℤ) (hp : NonnegativePrimitiveDirection p) :
    (primitiveSeedTrace M0 N0 p hp : ℝ) = 2 * Real.cosh (primitiveSeedLength M0 N0 p hp / 2) := by
  have ht : (3 : ℝ) ≤ primitiveSeedTrace M0 N0 p hp := by
    exact_mod_cast primitiveSeedTrace_ge_three M0 N0 h0 p hp
  have hh : primitiveSeedLength M0 N0 p hp / 2 = Real.arcosh ((primitiveSeedTrace M0 N0 p hp : ℝ) / 2) := by
    dsimp [primitiveSeedLength]
    ring
  rw [hh, Real.cosh_arcosh (by linarith)]
  ring

theorem SeededFarey.coordinate_left_nonnegativePrimitive {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (1, 0) (0, 1) M0 N0 u v M N) : NonnegativePrimitiveDirection u :=
  ⟨h.coordinate_nonnegative_labels.1, h.coordinate_nonnegative_labels.2.1,
    h.coordinate_primitive_labels.1⟩

theorem SeededFarey.coordinate_right_nonnegativePrimitive {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (1, 0) (0, 1) M0 N0 u v M N) : NonnegativePrimitiveDirection v :=
  ⟨h.coordinate_nonnegative_labels.2.2.1, h.coordinate_nonnegative_labels.2.2.2,
    h.coordinate_primitive_labels.2⟩

theorem SeededFarey.primitiveSeedMatrix_left {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (1, 0) (0, 1) M0 N0 u v M N) (hu : NonnegativePrimitiveDirection u) :
    primitiveSeedMatrix M0 N0 u hu = M :=
  primitiveSeedMatrix_eq_of_carries hu (Or.inl ⟨v, N, h⟩)

theorem SeededFarey.primitiveSeedMatrix_right {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (1, 0) (0, 1) M0 N0 u v M N) (hv : NonnegativePrimitiveDirection v) :
    primitiveSeedMatrix M0 N0 v hv = N :=
  primitiveSeedMatrix_eq_of_carries hv (Or.inr ⟨u, M, h⟩)

theorem SeededFarey.canonicalSeedTrace_fricke {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (1, 0) (0, 1) M0 N0 u v M N) (h0 : PositiveFrickePair M0 N0)
    (hu : NonnegativePrimitiveDirection u) (hv : NonnegativePrimitiveDirection v)
    (hs : NonnegativePrimitiveDirection (u + v)) :
    primitiveSeedTrace M0 N0 u hu ^ 2 + primitiveSeedTrace M0 N0 v hv ^ 2 +
      primitiveSeedTrace M0 N0 (u + v) hs ^ 2 =
      primitiveSeedTrace M0 N0 u hu * primitiveSeedTrace M0 N0 v hv * primitiveSeedTrace M0 N0 (u + v) hs := by
  simp only [primitiveSeedTrace, h.primitiveSeedMatrix_left, h.primitiveSeedMatrix_right,
    h.left.primitiveSeedMatrix_right]
  exact (h.positiveFrickePair h0).fricke

theorem SeededFarey.canonicalSeedMatrix_integral_ray {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (1, 0) (0, 1) M0 N0 u v M N) (n : ℕ)
    (hp : NonnegativePrimitiveDirection (n • u + v)) :
    primitiveSeedMatrix M0 N0 (n • u + v) hp = M ^ n * N :=
  (h.integral_ray n).primitiveSeedMatrix_right hp

theorem SeededFarey.canonicalSeedTrace_integral_ray {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (1, 0) (0, 1) M0 N0 u v M N) (n : ℕ)
    (hp : NonnegativePrimitiveDirection (n • u + v)) :
    primitiveSeedTrace M0 N0 (n • u + v) hp = (M ^ n * N).trace := by
  rw [primitiveSeedTrace, h.canonicalSeedMatrix_integral_ray n hp]

/-- The local strict length triangle holds for every positive Fricke seed,
including the mixed-sign seed whose initial product trace is 6. -/
theorem SeededFarey.canonicalSeedLength_strict_triangle
    {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : SeededFarey (1, 0) (0, 1) M0 N0 u v M N) (h0 : PositiveFrickePair M0 N0)
    (hu : NonnegativePrimitiveDirection u) (hv : NonnegativePrimitiveDirection v)
    (hs : NonnegativePrimitiveDirection (u + v)) :
    primitiveSeedLength M0 N0 (u + v) hs <
      primitiveSeedLength M0 N0 u hu + primitiveSeedLength M0 N0 v hv := by
  have htu : (3 : ℝ) ≤ primitiveSeedTrace M0 N0 u hu := by
    exact_mod_cast primitiveSeedTrace_ge_three M0 N0 h0 u hu
  have htv : (3 : ℝ) ≤ primitiveSeedTrace M0 N0 v hv := by
    exact_mod_cast primitiveSeedTrace_ge_three M0 N0 h0 v hv
  have hts : (3 : ℝ) ≤ primitiveSeedTrace M0 N0 (u + v) hs := by
    exact_mod_cast primitiveSeedTrace_ge_three M0 N0 h0 (u + v) hs
  have hf : (primitiveSeedTrace M0 N0 u hu : ℝ) ^ 2 +
      (primitiveSeedTrace M0 N0 v hv : ℝ) ^ 2 +
      (primitiveSeedTrace M0 N0 (u + v) hs : ℝ) ^ 2 =
      (primitiveSeedTrace M0 N0 u hu : ℝ) * primitiveSeedTrace M0 N0 v hv *
        primitiveSeedTrace M0 N0 (u + v) hs := by
    exact_mod_cast h.canonicalSeedTrace_fricke h0 hu hv hs
  exact fricke_trace_length_strict_triangle _ _ _ (by linarith) (by linarith) (by linarith) hf

end Markov
