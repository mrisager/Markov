import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.Tactic

noncomputable section
namespace Markov

/-- Two unit-disk boundary points on opposite sides of the real diameter
have an actual transverse chord intersection at strictly interior parameters. -/
theorem unitDisk_opposite_imaginary_chord_crossing
    (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hop : a.im * b.im < 0) :
    ∃ u v : unitInterval,
      0 < (u : ℝ) ∧ (u : ℝ) < 1 ∧ 0 < (v : ℝ) ∧ (v : ℝ) < 1 ∧
      (1-(u : ℝ)) • (-1 : ℂ) + (u : ℝ) • (1 : ℂ) =
        (1-(v : ℝ)) • a + (v : ℝ) • b ∧
      ((1 : ℂ)-(-1 : ℂ)).re * (b-a).im -
        ((1 : ℂ)-(-1 : ℂ)).im * (b-a).re ≠ 0 := by
  have han : a.im ≠ 0 := by intro h; rw [h, zero_mul] at hop; linarith
  have hbn : b.im ≠ 0 := by intro h; rw [h, mul_zero] at hop; linarith
  have hap : 0 < |a.im| := abs_pos.mpr han
  have hbp : 0 < |b.im| := abs_pos.mpr hbn
  have hd : 0 < |a.im| + |b.im| := add_pos hap hbp
  have hcancel : |b.im| * a.im + |a.im| * b.im = 0 := by
    rcases mul_neg_iff.mp hop with h | h
    · rw [abs_of_neg h.2, abs_of_pos h.1]; ring
    · rw [abs_of_pos h.2, abs_of_neg h.1]; ring
  let vreal : ℝ := |a.im| / (|a.im| + |b.im|)
  have hv0 : 0 < vreal := div_pos hap hd
  have hv1 : vreal < 1 := (div_lt_one hd).mpr (by linarith)
  let w : ℂ := (1-vreal) • a + vreal • b
  have hwi : w.im = 0 := by
    simp only [w, Complex.add_im]
    dsimp [vreal]
    field_simp [hd.ne']
    nlinarith [hcancel]
  have hne : a ≠ b := by intro h; rw [h] at hop; nlinarith [sq_nonneg b.im]
  have hw : ‖w‖ < 1 := norm_combo_lt_of_ne ha.le hb.le hne (sub_pos.mpr hv1) hv0 (by ring)
  have hre : -1 < w.re ∧ w.re < 1 := by
    have hh := abs_le.mp (Complex.abs_re_le_norm w)
    exact ⟨by linarith, by linarith⟩
  let ureal : ℝ := (w.re+1)/2
  have hu0 : 0 < ureal := by dsimp [ureal]; linarith [hre.1]
  have hu1 : ureal < 1 := by dsimp [ureal]; linarith [hre.2]
  refine ⟨⟨ureal, hu0.le, hu1.le⟩, ⟨vreal, hv0.le, hv1.le⟩,
    hu0, hu1, hv0, hv1, ?_, ?_⟩
  · change (1-ureal) • (-1 : ℂ) + ureal • (1 : ℂ) = w
    apply Complex.ext
    · simp only [Complex.add_re]
      dsimp [ureal]
      ring
    · simpa [Complex.real_smul] using hwi.symm
  · have him : b.im-a.im ≠ 0 := by intro h; have hh := sub_eq_zero.mp h; rw [hh] at hop; nlinarith [sq_nonneg a.im]
    simpa using mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) him

end Markov
