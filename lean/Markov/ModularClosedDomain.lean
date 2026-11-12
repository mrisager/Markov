import Markov.ModularTraceFundamentalRegion

/-! Closed standard modular-domain return estimates, retaining the
actual integral matrices and their central signs. No freeness of the
full modular action or polygon identification is assumed. -/

noncomputable section
open scoped MatrixGroups
open Set
namespace Markov

theorem modular_normSq_int_linear (z : UpperHalfPlane) (c d : ℤ) :
    Complex.normSq ((c : ℂ) * z + d) =
      ((c : ℝ) * z.re + (d : ℝ)) ^ 2 + ((c : ℝ) * z.im) ^ 2 := by
  simp [Complex.normSq_apply, pow_two]

theorem modularClosedDomain_twice_re_abs_le (z : UpperHalfPlane)
    (hz : z ∈ ModularGroup.fd) : |2 * z.re| ≤ 1 := by
  rw [abs_mul]
  norm_num
  linarith [hz.2]

/-- Every nonzero integral row has denominator norm at least one on
the actual closed standard modular domain. Coprimality is unnecessary. -/
theorem modularClosedDomain_normSq_linear_ge_one (z : UpperHalfPlane)
    (hz : z ∈ ModularGroup.fd) (c d : ℤ) (hcd : c ≠ 0 ∨ d ≠ 0) :
    1 ≤ Complex.normSq ((c : ℂ) * z + d) := by
  have hx := modularClosedDomain_twice_re_abs_le z hz
  have hnorm : 1 ≤ z.re ^ 2 + z.im ^ 2 := by
    simpa [Complex.normSq_apply, pow_two] using hz.1
  rw [modular_normSq_int_linear]
  by_cases hc : c = 0
  · have hd : d ≠ 0 := hcd.resolve_left (not_not.mpr hc)
    have hdZ : (1 : ℤ) ≤ d ^ 2 := by
      by_cases hp : 0 < d
      · have hh : 1 ≤ d := by omega
        nlinarith
      · have hh : d ≤ -1 := by omega
        nlinarith
    have hdR : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by exact_mod_cast hdZ
    simpa [hc] using hdR
  · by_cases hc1 : c = 1
    · have hd := Int.nneg_mul_add_sq_of_abs_le_one d hx
      norm_num [hc1]
      nlinarith
    · by_cases hcm : c = -1
      · have hd := Int.nneg_mul_add_sq_of_abs_le_one (-d) hx
        push_cast at hd
        norm_num [hcm]
        nlinarith
      · have hcZ : (4 : ℤ) ≤ c ^ 2 := by
          have hh : c ≤ -2 ∨ 2 ≤ c := by omega
          rcases hh with hh | hh <;> nlinarith
        have hcR : (4 : ℝ) ≤ (c : ℝ) ^ 2 := by exact_mod_cast hcZ
        have hy := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
        have hm := mul_le_mul_of_nonneg_right hcR (sq_nonneg z.im)
        nlinarith [sq_nonneg ((c : ℝ) * z.re + (d : ℝ))]

theorem modularClosedDomain_normSq_denom_ge_one (g : SL(2, ℤ))
    (z : UpperHalfPlane) (hz : z ∈ ModularGroup.fd) :
    1 ≤ Complex.normSq ((g 1 0 : ℂ) * z + g 1 1) := by
  apply modularClosedDomain_normSq_linear_ge_one z hz
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  by_contra h
  push_neg at h
  rw [h.1, h.2] at hdet
  norm_num at hdet

theorem modularClosedDomain_im_smul_le (g : SL(2, ℤ))
    (z : UpperHalfPlane) (hz : z ∈ ModularGroup.fd) : (g • z).im ≤ z.im := by
  rw [ModularGroup.im_smul_eq_div_normSq]
  apply div_le_self z.im_pos.le
  exact modularClosedDomain_normSq_denom_ge_one g z hz

theorem modularClosedReturn_im_eq (g : SL(2, ℤ)) (z : UpperHalfPlane)
    (hz : z ∈ ModularGroup.fd) (hgz : g • z ∈ ModularGroup.fd) :
    (g • z).im = z.im := by
  apply le_antisymm (modularClosedDomain_im_smul_le g z hz)
  simpa only [inv_smul_smul] using modularClosedDomain_im_smul_le g⁻¹ (g • z) hgz

theorem modularClosedReturn_normSq_denom_eq_one (g : SL(2, ℤ)) (z : UpperHalfPlane)
    (hz : z ∈ ModularGroup.fd) (hgz : g • z ∈ ModularGroup.fd) :
    Complex.normSq ((g 1 0 : ℂ) * z + g 1 1) = 1 := by
  have hi := modularClosedReturn_im_eq g z hz hgz
  rw [ModularGroup.im_smul_eq_div_normSq] at hi
  have hp : 0 < Complex.normSq ((g 1 0 : ℂ) * z + g 1 1) :=
    lt_of_lt_of_le (by norm_num) (modularClosedDomain_normSq_denom_ge_one g z hz)
  have he := (div_eq_iff hp.ne').mp hi
  change z.im = z.im * Complex.normSq ((g 1 0 : ℂ) * z + g 1 1) at he
  nlinarith [z.im_pos]

theorem modularClosedReturn_abs_c_le_one (g : SL(2, ℤ)) (z : UpperHalfPlane)
    (hz : z ∈ ModularGroup.fd) (hgz : g • z ∈ ModularGroup.fd) : |g 1 0| ≤ 1 := by
  have hn := modularClosedReturn_normSq_denom_eq_one g z hz hgz
  rw [modular_normSq_int_linear] at hn
  have hy := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  by_contra h
  have hc : g 1 0 ≤ -2 ∨ 2 ≤ g 1 0 := by
    rcases lt_abs.mp (lt_of_not_ge h) with hc | hc
    · right; omega
    · left; omega
  have hcZ : (4 : ℤ) ≤ (g 1 0) ^ 2 := by rcases hc with hc | hc <;> nlinarith
  have hcR : (4 : ℝ) ≤ (g 1 0 : ℝ) ^ 2 := by exact_mod_cast hcZ
  have hm := mul_le_mul_of_nonneg_right hcR (sq_nonneg z.im)
  nlinarith [sq_nonneg ((g 1 0 : ℝ) * z.re + (g 1 1 : ℝ))]

theorem modularClosedDomain_unit_translate_bounds (z : UpperHalfPlane)
    (hz : z ∈ ModularGroup.fd) (n : ℤ)
    (hn : Complex.normSq ((z : ℂ) + n) = 1) :
    |n| ≤ 1 ∧ |z.re + (n : ℝ)| ≤ 1 / 2 := by
  have he : (z.re + (n : ℝ)) ^ 2 + z.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using hn
  have hy := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  have hu2 : (z.re + (n : ℝ)) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith
  have hu : |z.re + (n : ℝ)| ≤ 1 / 2 := by
    simpa using (sq_le_sq.mp hu2)
  have hnR : |(n : ℝ)| ≤ 1 := by
    calc
      |(n : ℝ)| = |(z.re + (n : ℝ)) - z.re| := by congr 1; ring
      _ ≤ |z.re + (n : ℝ)| + |z.re| := abs_sub _ _
      _ ≤ 1 := by linarith [hz.2]
  exact ⟨by exact_mod_cast hnR, hu⟩

theorem modular_S_re_of_normSq_eq_one (z : UpperHalfPlane)
    (hz : Complex.normSq (z : ℂ) = 1) : (ModularGroup.S • z).re = -z.re := by
  rw [UpperHalfPlane.modular_S_smul]
  change Complex.re ((-(z : ℂ))⁻¹) = -z.re
  rw [Complex.inv_re, Complex.neg_re, Complex.normSq_neg, hz, div_one]
  rfl

theorem modularClosedReturn_c_one_data (g : SL(2, ℤ)) (z : UpperHalfPlane)
    (hz : z ∈ ModularGroup.fd) (hgz : g • z ∈ ModularGroup.fd) (hc : g 1 0 = 1) :
    |g 0 0| ≤ 1 ∧ |g 1 1| ≤ 1 ∧
      (g • z).re = -(z.re + (g 1 1 : ℝ)) + (g 0 0 : ℝ) := by
  have hn : Complex.normSq ((z : ℂ) + g 1 1) = 1 := by
    have hh := modularClosedReturn_normSq_denom_eq_one g z hz hgz
    simpa only [hc, Int.cast_one, one_mul] using hh
  obtain ⟨hd, hu⟩ := modularClosedDomain_unit_translate_bounds z hz (g 1 1) hn
  have hnt : Complex.normSq ((ModularGroup.T ^ (g 1 1) • z : UpperHalfPlane) : ℂ) = 1 := by
    rw [ModularGroup.coe_T_zpow_smul_eq]
    exact hn
  have hr : (g • z).re = -(z.re + (g 1 1 : ℝ)) + (g 0 0 : ℝ) := by
    nth_rw 1 [ModularGroup.g_eq_of_c_eq_one hc]
    rw [mul_smul, mul_smul,
      ModularGroup.re_T_zpow_smul, modular_S_re_of_normSq_eq_one _ hnt,
      ModularGroup.re_T_zpow_smul]
  have haR : |(g 0 0 : ℝ)| ≤ 1 := by
    calc
      |(g 0 0 : ℝ)| = |(g • z).re + (z.re + (g 1 1 : ℝ))| := by rw [hr]; congr 1; ring
      _ ≤ |(g • z).re| + |z.re + (g 1 1 : ℝ)| := abs_add_le _ _
      _ ≤ 1 := by linarith [hgz.2]
  exact ⟨by exact_mod_cast haR, hd, hr⟩

/-- The ten possible closed-domain return words, before the central sign. -/
def modularClosedReturnWords : Finset SL(2, ℤ) := by
  classical
  exact {1, ModularGroup.T, ModularGroup.T⁻¹, ModularGroup.S,
    ModularGroup.T * ModularGroup.S, ModularGroup.T⁻¹ * ModularGroup.S,
    ModularGroup.S * ModularGroup.T, ModularGroup.S * ModularGroup.T⁻¹,
    ModularGroup.T * ModularGroup.S * ModularGroup.T,
    ModularGroup.T⁻¹ * ModularGroup.S * ModularGroup.T⁻¹}

theorem modularClosedReturn_c_one_mem (g : SL(2, ℤ)) (z : UpperHalfPlane)
    (hz : z ∈ ModularGroup.fd) (hgz : g • z ∈ ModularGroup.fd) (hc : g 1 0 = 1) :
    g ∈ modularClosedReturnWords := by
  obtain ⟨ha, hd, hr⟩ := modularClosedReturn_c_one_data g z hz hgz hc
  have hacases : g 0 0 = -1 ∨ g 0 0 = 0 ∨ g 0 0 = 1 := by
    have hh := abs_le.mp ha
    omega
  have hdcases : g 1 1 = -1 ∨ g 1 1 = 0 ∨ g 1 1 = 1 := by
    have hh := abs_le.mp hd
    omega
  rcases hacases with ha | ha | ha <;> rcases hdcases with hd | hd | hd
  all_goals try solve
    | rw [ModularGroup.g_eq_of_c_eq_one hc, ha, hd]
      simp [modularClosedReturnWords]
  all_goals
    exfalso
    have hxlo := (abs_le.mp hz.2).1
    have hxhi := (abs_le.mp hz.2).2
    have hwlo := (abs_le.mp hgz.2).1
    have hwhi := (abs_le.mp hgz.2).2
    simp only [ha, hd, Int.cast_neg, Int.cast_one] at hr
    linarith

theorem modularInteger_eq_signed_T_zpow_of_c_eq_zero (g : SL(2, ℤ))
    (hc : g 1 0 = 0) : ∃ n : ℤ, g = ModularGroup.T ^ n ∨ g = -(ModularGroup.T ^ n) := by
  have had : g 0 0 * g 1 1 = 1 := by
    have hh := g.property
    simpa only [Matrix.det_fin_two, hc, mul_zero, sub_zero] using hh
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with ⟨ha, hd⟩ | ⟨ha, hd⟩
  · refine ⟨g 0 1, Or.inl ?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ModularGroup.coe_T_zpow, ha, hd, hc]
  · refine ⟨-(g 0 1), Or.inr ?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_neg, ModularGroup.coe_T_zpow, ha, hd, hc]

theorem modularClosedReturn_c_zero_word (g : SL(2, ℤ)) (z : UpperHalfPlane)
    (hz : z ∈ ModularGroup.fd) (hgz : g • z ∈ ModularGroup.fd) (hc : g 1 0 = 0) :
    ∃ n : ℤ, |n| ≤ 1 ∧ (g = ModularGroup.T ^ n ∨ g = -(ModularGroup.T ^ n)) ∧
      (g • z).re = z.re + n := by
  obtain ⟨n, hn⟩ := modularInteger_eq_signed_T_zpow_of_c_eq_zero g hc
  have hact : g • z = ModularGroup.T ^ n • z := by
    rcases hn with h | h
    · rw [h]
    · rw [h, ModularGroup.SL_neg_smul]
  have hr : (g • z).re = z.re + n := by rw [hact, ModularGroup.re_T_zpow_smul]
  have hnR : |(n : ℝ)| ≤ 1 := by
    calc
      |(n : ℝ)| = |(g • z).re - z.re| := by rw [hr]; congr 1; ring
      _ ≤ |(g • z).re| + |z.re| := abs_sub _ _
      _ ≤ 1 := by linarith [hz.2, hgz.2]
  exact ⟨n, by exact_mod_cast hnR, hn, hr⟩

/-- Full literal matrix return classification, preserving the central sign
and the possible noncentral elliptic boundary stabilizers. -/
theorem modularClosedReturn_signed_word (g : SL(2, ℤ)) (z : UpperHalfPlane)
    (hz : z ∈ ModularGroup.fd) (hgz : g • z ∈ ModularGroup.fd) :
    ∃ h ∈ modularClosedReturnWords, g = h ∨ g = -h := by
  have hc := modularClosedReturn_abs_c_le_one g z hz hgz
  by_cases hc0 : g 1 0 = 0
  · obtain ⟨n, hn, hgn, _⟩ := modularClosedReturn_c_zero_word g z hz hgz hc0
    have hcases : n = -1 ∨ n = 0 ∨ n = 1 := by
      have hh := abs_le.mp hn
      omega
    refine ⟨ModularGroup.T ^ n, ?_, hgn⟩
    rcases hcases with rfl | rfl | rfl <;> simp [modularClosedReturnWords]
  · have hcases : g 1 0 = 1 ∨ g 1 0 = -1 := by
      have hh := abs_le.mp hc
      omega
    rcases hcases with hc1 | hcm
    · exact ⟨g, modularClosedReturn_c_one_mem g z hz hgz hc1, Or.inl rfl⟩
    · have hc1 : (-g) 1 0 = 1 := by change -(g 1 0) = 1; omega
      have hneg : (-g) • z ∈ ModularGroup.fd := by
        simpa only [ModularGroup.SL_neg_smul] using hgz
      exact ⟨-g, modularClosedReturn_c_one_mem (-g) z hz hneg hc1, Or.inr (neg_neg g).symm⟩

end Markov
