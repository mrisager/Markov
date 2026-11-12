import Markov.FareyCoverage
import Markov.UnimodularPartners

/-! Consistency of the labelled positive Farey-tree construction. -/

namespace Markov

/-- A generated label is never the zero vector. -/
theorem FareyHolonomy.nonzero_labels {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : FareyHolonomy u v M N) : u ≠ 0 ∧ v ≠ 0 := by
  have hd := h.det_eq_one
  constructor <;> intro hz <;> simp [hz, intDet] at hd

/-- Determinant-one matrices permit cancellation without assuming a
field of entries. -/
theorem intMatrix_left_cancel {M N P : IntMatrixTwo} (hM : M.det = 1)
    (h : M * N = M * P) : N = P := by
  have hh := congrArg (fun X : IntMatrixTwo => M.adjugate * X) h
  simpa only [← Matrix.mul_assoc, Matrix.adjugate_mul, hM, one_smul, one_mul] using hh

theorem intMatrix_right_cancel {M N P : IntMatrixTwo} (hM : M.det = 1)
    (h : N * M = P * M) : N = P := by
  have hh := congrArg (fun X : IntMatrixTwo => X * M.adjugate) h
  simpa only [Matrix.mul_assoc, Matrix.mul_adjugate, hM, one_smul, mul_one] using hh

theorem nonnegative_not_left_seed (u v : ℤ × ℤ) (hv : 0 ≤ v.1)
    (hu : u = (1, 0)) (hs : u + v = (0, 1)) : False := by
  have he := congrArg Prod.fst hs
  simp only [Prod.fst_add, hu] at he
  omega

theorem nonnegative_not_right_seed (u v : ℤ × ℤ) (hu : 0 ≤ u.2)
    (hs : u + v = (1, 0)) (hv : v = (0, 1)) : False := by
  have he := congrArg Prod.snd hs
  simp only [Prod.snd_add, hv] at he
  omega

theorem nonnegative_left_right_disjoint (u v u' v' : ℤ × ℤ)
    (hv1 : 0 ≤ v.1) (hv2 : 0 ≤ v.2) (hu1 : 0 ≤ u'.1) (hu2 : 0 ≤ u'.2)
    (hv0 : v ≠ 0) (he : u = u' + v') (he' : u + v = v') : False := by
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  have h3 := congrArg Prod.fst he'
  have h4 := congrArg Prod.snd he'
  simp only [Prod.fst_add, Prod.snd_add] at h1 h2 h3 h4
  apply hv0
  apply Prod.ext <;> simp only [Prod.fst_zero, Prod.snd_zero] <;> omega

/-- The direction pair determines the actual matrices uniquely, not merely
their traces. This is a statement about the constructed tree. -/
theorem FareyHolonomy.matrices_unique_general {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : FareyHolonomy u v M N) :
    ∀ {u' v' : ℤ × ℤ} {M' N' : IntMatrixTwo}, FareyHolonomy u' v' M' N' →
      u = u' → v = v' → M = M' ∧ N = N' := by
  induction h with
  | seed =>
    intro u' v' M' N' h' he he'
    cases h' with
    | seed => exact ⟨rfl, rfl⟩
    | @left a b P Q hp =>
      exact False.elim (nonnegative_not_left_seed _ _ hp.nonnegative_labels.2.2.1 he.symm he'.symm)
    | @right a b P Q hp =>
      exact False.elim (nonnegative_not_right_seed _ _ hp.nonnegative_labels.2.1 he.symm he'.symm)
  | @left u v M N hp ih =>
    intro u' v' M' N' h' he he'
    cases h' with
    | seed =>
      exact False.elim (nonnegative_not_left_seed u v hp.nonnegative_labels.2.2.1 he he')
    | @left a b P Q hq =>
      rcases ih hq he (by rw [he] at he'; exact add_left_cancel he') with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
    | @right a b P Q hq =>
      exact False.elim (nonnegative_left_right_disjoint _ _ _ _
        hp.nonnegative_labels.2.2.1 hp.nonnegative_labels.2.2.2
        hq.nonnegative_labels.1 hq.nonnegative_labels.2.1 hp.nonzero_labels.2 he he')
  | @right u v M N hp ih =>
    intro u' v' M' N' h' he he'
    cases h' with
    | seed =>
      exact False.elim (nonnegative_not_right_seed u v hp.nonnegative_labels.2.1 he he')
    | @left a b P Q hq =>
      exact False.elim (nonnegative_left_right_disjoint _ _ _ _
        hq.nonnegative_labels.2.2.1 hq.nonnegative_labels.2.2.2
        hp.nonnegative_labels.1 hp.nonnegative_labels.2.1 hq.nonzero_labels.2 he.symm he'.symm)
    | @right a b P Q hq =>
      rcases ih hq (by rw [he'] at he; exact add_right_cancel he) he' with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩

theorem FareyHolonomy.matrices_unique {u v : ℤ × ℤ} {M N M' N' : IntMatrixTwo}
    (h : FareyHolonomy u v M N) (h' : FareyHolonomy u v M' N') : M = M' ∧ N = N' :=
  h.matrices_unique_general h' rfl rfl

/-- Iteration on the other side of a Farey pair fixes its second matrix. -/
theorem FareyHolonomy.right_integral_ray {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : FareyHolonomy u v M N) (n : ℕ) :
    FareyHolonomy (u + n • v) v (M * N ^ n) N := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    have hu : u + (n + 1) • v = (u + n • v) + v := by
      rw [add_nsmul, one_nsmul]
      abel
    rw [hu, pow_succ, ← Matrix.mul_assoc]
    exact ih.right

theorem toNat_nsmul_eq_zsmul (k : ℤ) (hk : 0 ≤ k) (u : ℤ × ℤ) :
    k.toNat • u = k • u := by
  rw [← natCast_zsmul, Int.toNat_of_nonneg hk]

/-- A direction's matrix is independent of its positive-side partner. -/
theorem FareyHolonomy.first_matrix_unique {u v w : ℤ × ℤ} {M N P Q : IntMatrixTwo}
    (h : FareyHolonomy u v M N) (h' : FareyHolonomy u w P Q) : M = P := by
  obtain ⟨k, he⟩ := unimodular_partners_exists_shear u v w h.det_eq_one h'.det_eq_one
  by_cases hk : 0 ≤ k
  · have hv : k.toNat • u + w = v := by
      rw [toNat_nsmul_eq_zsmul k hk]
      rw [he, add_comm]
    have hr := h'.integral_ray k.toNat
    rw [hv] at hr
    exact (h.matrices_unique hr).1
  · have hneg : 0 ≤ -k := by omega
    have hw : (-k).toNat • u + v = w := by
      rw [toNat_nsmul_eq_zsmul (-k) hneg, he, neg_smul]
      abel
    have hr := h.integral_ray (-k).toNat
    rw [hw] at hr
    exact (hr.matrices_unique h').1

/-- A direction's matrix is independent of its negative-side partner. -/
theorem FareyHolonomy.second_matrix_unique {u v w : ℤ × ℤ} {M N P Q : IntMatrixTwo}
    (h : FareyHolonomy u v M N) (h' : FareyHolonomy w v P Q) : N = Q := by
  have hvu : intDet v u = -1 := by
    have hh := h.det_eq_one
    dsimp [intDet] at *
    linarith
  have hvw : intDet v w = -1 := by
    have hh := h'.det_eq_one
    dsimp [intDet] at *
    linarith
  obtain ⟨k, he⟩ := neg_unimodular_partners_exists_shear v u w hvu hvw
  by_cases hk : 0 ≤ k
  · have hu : w + k.toNat • v = u := by
      rw [toNat_nsmul_eq_zsmul k hk, he]
    have hr := h'.right_integral_ray k.toNat
    rw [hu] at hr
    exact (h.matrices_unique hr).2
  · have hneg : 0 ≤ -k := by omega
    have hw : u + (-k).toNat • v = w := by
      rw [toNat_nsmul_eq_zsmul (-k) hneg, he, neg_smul]
      abel
    have hr := h.right_integral_ray (-k).toNat
    rw [hw] at hr
    exact (hr.matrices_unique h').2

/-- A positive-mass primitive direction has only one oriented unimodular
split into two positive-mass directions. -/
theorem unimodular_positive_sum_unique (u v a b : ℤ × ℤ)
    (hu : 0 < u.1 + u.2) (hv : 0 < v.1 + v.2)
    (ha : 0 < a.1 + a.2) (hb : 0 < b.1 + b.2)
    (huv : intDet u v = 1) (hab : intDet a b = 1)
    (hs : u + v = a + b) : u = a ∧ v = b := by
  have hpu : intDet (u + v) u = -1 := by
    simp only [intDet, Prod.fst_add, Prod.snd_add] at *
    nlinarith
  have hpa : intDet (u + v) a = -1 := by
    rw [hs]
    simp only [intDet, Prod.fst_add, Prod.snd_add] at *
    nlinarith
  obtain ⟨k, hk⟩ := neg_unimodular_partners_exists_shear (u + v) u a hpu hpa
  have h1 := congrArg Prod.fst hk
  have h2 := congrArg Prod.snd hk
  simp [zsmul_eq_mul] at h1 h2
  have hm : u.1 + u.2 = a.1 + a.2 + k * (u.1 + u.2 + v.1 + v.2) := by
    nlinarith
  have hs1 := congrArg Prod.fst hs
  have hs2 := congrArg Prod.snd hs
  simp only [Prod.fst_add, Prod.snd_add] at hs1 hs2
  have hsum : u.1 + u.2 + v.1 + v.2 = a.1 + a.2 + b.1 + b.2 := by omega
  have hp : 0 ≤ u.1 + u.2 + v.1 + v.2 := by omega
  have hk0 : k = 0 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hn | hn
    · have hh := mul_nonneg (show 0 ≤ -k - 1 by omega) hp
      nlinarith
    · have hh := mul_nonneg (show 0 ≤ k - 1 by omega) hp
      nlinarith
  rw [hk0, zero_smul, add_zero] at hk
  exact ⟨hk, by rw [hk] at hs; exact add_left_cancel hs⟩

theorem FareyHolonomy.positive_mass {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : FareyHolonomy u v M N) : 0 < u.1 + u.2 ∧ 0 < v.1 + v.2 := by
  rcases h.nonnegative_labels with ⟨hu1, hu2, hv1, hv2⟩
  have hd := h.det_eq_one
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

/-- A direction has the same matrix when it occurs on opposite sides of two
Farey edges. The birth edge is determined by its positive unimodular split. -/
theorem FareyHolonomy.cross_matrix_unique_general {u v : ℤ × ℤ} {M N : IntMatrixTwo}
    (h : FareyHolonomy u v M N) :
    ∀ {a b : ℤ × ℤ} {P Q : IntMatrixTwo}, FareyHolonomy a b P Q → u = b → M = Q := by
  induction h with
  | seed =>
    intro a b P Q h' he
    have hd := h'.det_eq_one
    rw [← he] at hd
    have ha := h'.nonnegative_labels.2.1
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
      rcases hp.positive_mass with ⟨hu, hv⟩
      omega
    | left hq _ =>
      intro he
      have hs := unimodular_positive_sum_unique _ _ _ _ hp.positive_mass.1 hp.positive_mass.2
        hq.positive_mass.1 hq.positive_mass.2 hp.det_eq_one hq.det_eq_one he
      rcases hp.matrices_unique_general hq hs.1 hs.2 with ⟨hm, hn⟩
      rw [hm, hn]
    | right hq ih =>
      intro he
      exact ih he

theorem FareyHolonomy.cross_matrix_unique {u v w : ℤ × ℤ} {M N P Q : IntMatrixTwo}
    (h : FareyHolonomy u v M N) (h' : FareyHolonomy w u P Q) : M = Q :=
  h.cross_matrix_unique_general h' rfl

end Markov
