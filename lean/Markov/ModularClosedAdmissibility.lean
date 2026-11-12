import Markov.ModularClosedDomain

/-! Exact closed standard modular-domain return conditions for the
ten actual words. The central sign and elliptic corner possibilities
are retained. No polygon coverage or surface classification is asserted. -/

noncomputable section
open scoped MatrixGroups
open Set
namespace Markov

theorem modular_normSq_T_smul (z : UpperHalfPlane) :
    Complex.normSq ((ModularGroup.T • z : UpperHalfPlane) : ℂ) =
      Complex.normSq (z : ℂ) + 2 * z.re + 1 := by
  simp only [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  rw [ModularGroup.re_T_smul, ModularGroup.im_T_smul]
  ring

theorem modular_normSq_T_inv_smul (z : UpperHalfPlane) :
    Complex.normSq ((ModularGroup.T⁻¹ • z : UpperHalfPlane) : ℂ) =
      Complex.normSq (z : ℂ) - 2 * z.re + 1 := by
  simp only [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  rw [ModularGroup.re_T_inv_smul, ModularGroup.im_T_inv_smul]
  ring

theorem modular_normSq_S_smul (z : UpperHalfPlane) :
    Complex.normSq ((ModularGroup.S • z : UpperHalfPlane) : ℂ) =
      (Complex.normSq (z : ℂ))⁻¹ := by
  rw [UpperHalfPlane.modular_S_smul]
  change Complex.normSq ((-(z : ℂ))⁻¹) = _
  rw [Complex.normSq_inv, Complex.normSq_neg]

theorem modularClosedDomain_T_return_iff (z : UpperHalfPlane) (hz : z ∈ ModularGroup.fd) :
    ModularGroup.T • z ∈ ModularGroup.fd ↔ z.re = -1 / 2 := by
  constructor
  · intro h
    have hr := (abs_le.mp h.2).2
    rw [ModularGroup.re_T_smul] at hr
    linarith [(abs_le.mp hz.2).1]
  · intro hr
    constructor
    · rw [modular_normSq_T_smul, hr]
      linarith [hz.1]
    · rw [ModularGroup.re_T_smul, hr]
      norm_num

theorem modularClosedDomain_T_inv_return_iff (z : UpperHalfPlane)
    (hz : z ∈ ModularGroup.fd) :
    ModularGroup.T⁻¹ • z ∈ ModularGroup.fd ↔ z.re = 1 / 2 := by
  constructor
  · intro h
    have hr := (abs_le.mp h.2).1
    rw [ModularGroup.re_T_inv_smul] at hr
    linarith [(abs_le.mp hz.2).2]
  · intro hr
    constructor
    · rw [modular_normSq_T_inv_smul, hr]
      linarith [hz.1]
    · rw [ModularGroup.re_T_inv_smul, hr]
      norm_num

theorem modularClosedDomain_S_return_iff (z : UpperHalfPlane) (hz : z ∈ ModularGroup.fd) :
    ModularGroup.S • z ∈ ModularGroup.fd ↔ Complex.normSq (z : ℂ) = 1 := by
  constructor
  · intro h
    have hh := modularClosedReturn_normSq_denom_eq_one ModularGroup.S z hz h
    simpa [ModularGroup.coe_S] using hh
  · intro hc
    constructor
    · rw [modular_normSq_S_smul, hc]
      norm_num
    · rw [modular_S_re_of_normSq_eq_one z hc, abs_neg]
      exact hz.2

theorem modularClosedDomain_T_unit_iff (z : UpperHalfPlane) (hz : z ∈ ModularGroup.fd) :
    Complex.normSq ((ModularGroup.T • z : UpperHalfPlane) : ℂ) = 1 ↔
      Complex.normSq (z : ℂ) = 1 ∧ z.re = -1 / 2 := by
  rw [modular_normSq_T_smul]
  constructor
  · intro h
    constructor <;> linarith [hz.1, (abs_le.mp hz.2).1]
  · rintro ⟨hc, hr⟩
    rw [hc, hr]
    norm_num

theorem modularClosedDomain_T_inv_unit_iff (z : UpperHalfPlane) (hz : z ∈ ModularGroup.fd) :
    Complex.normSq ((ModularGroup.T⁻¹ • z : UpperHalfPlane) : ℂ) = 1 ↔
      Complex.normSq (z : ℂ) = 1 ∧ z.re = 1 / 2 := by
  rw [modular_normSq_T_inv_smul]
  constructor
  · intro h
    constructor <;> linarith [hz.1, (abs_le.mp hz.2).2]
  · rintro ⟨hc, hr⟩
    rw [hc, hr]
    norm_num

/-- Necessary unit-circle data for an actual normalized return word,
reusing the proved closed-return denominator equality. -/
theorem modularClosedReturn_TST_unit (a d : ℤ) (z : UpperHalfPlane)
    (hz : z ∈ ModularGroup.fd)
    (h : (ModularGroup.T ^ a * ModularGroup.S * ModularGroup.T ^ d) • z ∈ ModularGroup.fd) :
    Complex.normSq ((ModularGroup.T ^ d • z : UpperHalfPlane) : ℂ) = 1 := by
  let g : SL(2, ℤ) := ModularGroup.T ^ a * ModularGroup.S * ModularGroup.T ^ d
  have hc : g 1 0 = 1 := by
    simp [g, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow,
      ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two]
  have hd : g 1 1 = d := by
    simp [g, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow,
      ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two]
  have he := modularClosedReturn_normSq_denom_eq_one g z hz h
  rw [ModularGroup.coe_T_zpow_smul_eq]
  simpa only [hc, hd, Int.cast_one, one_mul] using he

theorem modularClosedDomain_TS_return_iff (z : UpperHalfPlane) (hz : z ∈ ModularGroup.fd) :
    (ModularGroup.T * ModularGroup.S) • z ∈ ModularGroup.fd ↔
      Complex.normSq (z : ℂ) = 1 ∧ z.re = 1 / 2 := by
  constructor
  · intro h
    have hc : Complex.normSq (z : ℂ) = 1 := by
      simpa only [zpow_zero, one_smul] using
        modularClosedReturn_TST_unit 1 0 z hz (by
          simpa only [zpow_one, zpow_zero, mul_one] using h)
    have hs := (modularClosedDomain_S_return_iff z hz).mpr hc
    have ht : ModularGroup.T • (ModularGroup.S • z) ∈ ModularGroup.fd := by
      simpa only [mul_smul] using h
    have hr := (modularClosedDomain_T_return_iff _ hs).mp ht
    rw [modular_S_re_of_normSq_eq_one z hc] at hr
    exact ⟨hc, by linarith⟩
  · rintro ⟨hc, hr⟩
    have hs := (modularClosedDomain_S_return_iff z hz).mpr hc
    rw [mul_smul]
    apply (modularClosedDomain_T_return_iff _ hs).mpr
    rw [modular_S_re_of_normSq_eq_one z hc, hr]
    norm_num

theorem modularClosedDomain_T_inv_S_return_iff (z : UpperHalfPlane)
    (hz : z ∈ ModularGroup.fd) :
    (ModularGroup.T⁻¹ * ModularGroup.S) • z ∈ ModularGroup.fd ↔
      Complex.normSq (z : ℂ) = 1 ∧ z.re = -1 / 2 := by
  constructor
  · intro h
    have hc : Complex.normSq (z : ℂ) = 1 := by
      simpa only [zpow_zero, one_smul] using
        modularClosedReturn_TST_unit (-1) 0 z hz (by
          simpa only [zpow_neg_one, zpow_zero, mul_one] using h)
    have hs := (modularClosedDomain_S_return_iff z hz).mpr hc
    have ht : ModularGroup.T⁻¹ • (ModularGroup.S • z) ∈ ModularGroup.fd := by
      simpa only [mul_smul] using h
    have hr := (modularClosedDomain_T_inv_return_iff _ hs).mp ht
    rw [modular_S_re_of_normSq_eq_one z hc] at hr
    exact ⟨hc, by linarith⟩
  · rintro ⟨hc, hr⟩
    have hs := (modularClosedDomain_S_return_iff z hz).mpr hc
    rw [mul_smul]
    apply (modularClosedDomain_T_inv_return_iff _ hs).mpr
    rw [modular_S_re_of_normSq_eq_one z hc, hr]
    norm_num

theorem modularClosedDomain_ST_return_iff (z : UpperHalfPlane) (hz : z ∈ ModularGroup.fd) :
    (ModularGroup.S * ModularGroup.T) • z ∈ ModularGroup.fd ↔
      Complex.normSq (z : ℂ) = 1 ∧ z.re = -1 / 2 := by
  constructor
  · intro h
    apply (modularClosedDomain_T_unit_iff z hz).mp
    simpa only [zpow_one] using modularClosedReturn_TST_unit 0 1 z hz (by
      simpa only [zpow_zero, one_mul, zpow_one] using h)
  · rintro ⟨hc, hr⟩
    have ht := (modularClosedDomain_T_return_iff z hz).mpr hr
    have hn := (modularClosedDomain_T_unit_iff z hz).mpr ⟨hc, hr⟩
    simpa only [mul_smul] using (modularClosedDomain_S_return_iff _ ht).mpr hn

theorem modularClosedDomain_ST_inv_return_iff (z : UpperHalfPlane)
    (hz : z ∈ ModularGroup.fd) :
    (ModularGroup.S * ModularGroup.T⁻¹) • z ∈ ModularGroup.fd ↔
      Complex.normSq (z : ℂ) = 1 ∧ z.re = 1 / 2 := by
  constructor
  · intro h
    apply (modularClosedDomain_T_inv_unit_iff z hz).mp
    simpa only [zpow_neg_one] using modularClosedReturn_TST_unit 0 (-1) z hz (by
      simpa only [zpow_zero, one_mul, zpow_neg_one] using h)
  · rintro ⟨hc, hr⟩
    have ht := (modularClosedDomain_T_inv_return_iff z hz).mpr hr
    have hn := (modularClosedDomain_T_inv_unit_iff z hz).mpr ⟨hc, hr⟩
    simpa only [mul_smul] using (modularClosedDomain_S_return_iff _ ht).mpr hn

theorem modularClosedDomain_TST_return_iff (z : UpperHalfPlane)
    (hz : z ∈ ModularGroup.fd) :
    (ModularGroup.T * ModularGroup.S * ModularGroup.T) • z ∈ ModularGroup.fd ↔
      Complex.normSq (z : ℂ) = 1 ∧ z.re = -1 / 2 := by
  constructor
  · intro h
    apply (modularClosedDomain_T_unit_iff z hz).mp
    simpa only [zpow_one] using modularClosedReturn_TST_unit 1 1 z hz (by
      simpa only [zpow_one] using h)
  · rintro ⟨hc, hr⟩
    have ht := (modularClosedDomain_T_return_iff z hz).mpr hr
    have hn := (modularClosedDomain_T_unit_iff z hz).mpr ⟨hc, hr⟩
    have hs := (modularClosedDomain_S_return_iff _ ht).mpr hn
    have hsr : (ModularGroup.S • (ModularGroup.T • z)).re = -1 / 2 := by
      rw [modular_S_re_of_normSq_eq_one _ hn, ModularGroup.re_T_smul, hr]
      norm_num
    simpa only [mul_smul] using (modularClosedDomain_T_return_iff _ hs).mpr hsr

theorem modularClosedDomain_T_inv_S_T_inv_return_iff (z : UpperHalfPlane)
    (hz : z ∈ ModularGroup.fd) :
    (ModularGroup.T⁻¹ * ModularGroup.S * ModularGroup.T⁻¹) • z ∈ ModularGroup.fd ↔
      Complex.normSq (z : ℂ) = 1 ∧ z.re = 1 / 2 := by
  constructor
  · intro h
    apply (modularClosedDomain_T_inv_unit_iff z hz).mp
    simpa only [zpow_neg_one] using modularClosedReturn_TST_unit (-1) (-1) z hz (by
      simpa only [zpow_neg_one] using h)
  · rintro ⟨hc, hr⟩
    have ht := (modularClosedDomain_T_inv_return_iff z hz).mpr hr
    have hn := (modularClosedDomain_T_inv_unit_iff z hz).mpr ⟨hc, hr⟩
    have hs := (modularClosedDomain_S_return_iff _ ht).mpr hn
    have hsr : (ModularGroup.S • (ModularGroup.T⁻¹ • z)).re = 1 / 2 := by
      rw [modular_S_re_of_normSq_eq_one _ hn, ModularGroup.re_T_inv_smul, hr]
      norm_num
    simpa only [mul_smul] using (modularClosedDomain_T_inv_return_iff _ hs).mpr hsr

/-- The literal word-labelled side and corner conditions. In particular,
the nontrivial elliptic stabilizers are not replaced by endpoint equality. -/
def ModularClosedAdmissible (g : SL(2, ℤ)) (z : UpperHalfPlane) : Prop :=
  g = 1 ∨
    (g = ModularGroup.T ∧ z.re = -1 / 2) ∨
    (g = ModularGroup.T⁻¹ ∧ z.re = 1 / 2) ∨
    (g = ModularGroup.S ∧ Complex.normSq (z : ℂ) = 1) ∨
    (g = ModularGroup.T * ModularGroup.S ∧
      Complex.normSq (z : ℂ) = 1 ∧ z.re = 1 / 2) ∨
    (g = ModularGroup.T⁻¹ * ModularGroup.S ∧
      Complex.normSq (z : ℂ) = 1 ∧ z.re = -1 / 2) ∨
    (g = ModularGroup.S * ModularGroup.T ∧
      Complex.normSq (z : ℂ) = 1 ∧ z.re = -1 / 2) ∨
    (g = ModularGroup.S * ModularGroup.T⁻¹ ∧
      Complex.normSq (z : ℂ) = 1 ∧ z.re = 1 / 2) ∨
    (g = ModularGroup.T * ModularGroup.S * ModularGroup.T ∧
      Complex.normSq (z : ℂ) = 1 ∧ z.re = -1 / 2) ∨
    (g = ModularGroup.T⁻¹ * ModularGroup.S * ModularGroup.T⁻¹ ∧
      Complex.normSq (z : ℂ) = 1 ∧ z.re = 1 / 2)

theorem ModularClosedAdmissible.word_mem {g : SL(2, ℤ)} {z : UpperHalfPlane}
    (h : ModularClosedAdmissible g z) : g ∈ modularClosedReturnWords := by
  classical
  rcases h with rfl | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ |
    ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;>
    simp [modularClosedReturnWords]

theorem ModularClosedAdmissible.returns {g : SL(2, ℤ)} {z : UpperHalfPlane}
    (h : ModularClosedAdmissible g z) (hz : z ∈ ModularGroup.fd) :
    g • z ∈ ModularGroup.fd := by
  rcases h with rfl | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ |
    ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · simpa only [one_smul] using hz
  · exact (modularClosedDomain_T_return_iff z hz).mpr h
  · exact (modularClosedDomain_T_inv_return_iff z hz).mpr h
  · exact (modularClosedDomain_S_return_iff z hz).mpr h
  · exact (modularClosedDomain_TS_return_iff z hz).mpr h
  · exact (modularClosedDomain_T_inv_S_return_iff z hz).mpr h
  · exact (modularClosedDomain_ST_return_iff z hz).mpr h
  · exact (modularClosedDomain_ST_inv_return_iff z hz).mpr h
  · exact (modularClosedDomain_TST_return_iff z hz).mpr h
  · exact (modularClosedDomain_T_inv_S_T_inv_return_iff z hz).mpr h

theorem modularClosedDomain_return_admissible_of_word (g : SL(2, ℤ))
    (z : UpperHalfPlane) (hz : z ∈ ModularGroup.fd) (hg : g ∈ modularClosedReturnWords)
    (hret : g • z ∈ ModularGroup.fd) : ModularClosedAdmissible g z := by
  classical
  simp only [modularClosedReturnWords, Finset.mem_insert, Finset.mem_singleton] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · have h := (modularClosedDomain_T_return_iff z hz).mp hret
    unfold ModularClosedAdmissible
    aesop
  · have h := (modularClosedDomain_T_inv_return_iff z hz).mp hret
    unfold ModularClosedAdmissible
    aesop
  · have h := (modularClosedDomain_S_return_iff z hz).mp hret
    unfold ModularClosedAdmissible
    aesop
  · have h := (modularClosedDomain_TS_return_iff z hz).mp hret
    unfold ModularClosedAdmissible
    aesop
  · have h := (modularClosedDomain_T_inv_S_return_iff z hz).mp hret
    unfold ModularClosedAdmissible
    aesop
  · have h := (modularClosedDomain_ST_return_iff z hz).mp hret
    unfold ModularClosedAdmissible
    aesop
  · have h := (modularClosedDomain_ST_inv_return_iff z hz).mp hret
    unfold ModularClosedAdmissible
    aesop
  · have h := (modularClosedDomain_TST_return_iff z hz).mp hret
    unfold ModularClosedAdmissible
    aesop
  · have h := (modularClosedDomain_T_inv_S_T_inv_return_iff z hz).mp hret
    unfold ModularClosedAdmissible
    aesop

theorem modularClosedDomain_word_return_iff_admissible (g : SL(2, ℤ))
    (z : UpperHalfPlane) (hz : z ∈ ModularGroup.fd) (hg : g ∈ modularClosedReturnWords) :
    g • z ∈ ModularGroup.fd ↔ ModularClosedAdmissible g z :=
  ⟨modularClosedDomain_return_admissible_of_word g z hz hg, fun h => h.returns hz⟩

theorem modularClosedDomain_neg_return_iff (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    (-g) • z ∈ ModularGroup.fd ↔ g • z ∈ ModularGroup.fd := by
  rw [ModularGroup.SL_neg_smul]

/-- The complete signed actual-matrix return classifier with the exact
side and corner admissibility conditions, in both directions. -/
theorem modularClosedDomain_signed_return_iff (g : SL(2, ℤ))
    (z : UpperHalfPlane) (hz : z ∈ ModularGroup.fd) :
    g • z ∈ ModularGroup.fd ↔
      ∃ h ∈ modularClosedReturnWords, (g = h ∨ g = -h) ∧ ModularClosedAdmissible h z := by
  constructor
  · intro hret
    obtain ⟨h, hh, hgh⟩ := modularClosedReturn_signed_word g z hz hret
    have hret' : h • z ∈ ModularGroup.fd := by
      rcases hgh with heq | heq
      · simpa only [heq] using hret
      · simpa only [heq, ModularGroup.SL_neg_smul] using hret
    exact ⟨h, hh, hgh, modularClosedDomain_return_admissible_of_word h z hz hh hret'⟩
  · rintro ⟨h, _, hgh, hadm⟩
    have hret := hadm.returns hz
    rcases hgh with rfl | rfl
    · exact hret
    · simpa only [ModularGroup.SL_neg_smul] using hret

end Markov
