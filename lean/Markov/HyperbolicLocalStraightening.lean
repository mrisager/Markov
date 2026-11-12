import Markov.HyperbolicVerticalContinuation
import Markov.UpperHalfPlanePairVerticalization

/-! Actual initial vertical germs and global metric straightening for real
locally unit-speed curves. No quotient or simplicity conclusion is asserted. -/

noncomputable section
open Set Metric
open scoped MatrixGroups
namespace Markov

/-- A distance-preserving interval whose endpoints are vertically ordered
is the positively oriented vertical axis with its exact logarithmic shift. -/
theorem upperHalfPlane_vertical_interval_eq
    (γ : ℝ → UpperHalfPlane) (a b : ℝ) (hab : a < b)
    (hmetric : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, dist (γ s) (γ t) = dist s t)
    (ha0 : (γ a).re = 0) (hb0 : (γ b).re = 0) (hh : (γ a).im < (γ b).im) :
    ∀ t ∈ Set.Icc a b,
      γ t = hyperbolicVerticalAxis (t + (Real.log (γ a).im - a)) := by
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab.le⟩
  have hb : b ∈ Set.Icc a b := ⟨hab.le, le_rfl⟩
  have hlog : Real.log (γ a).im < Real.log (γ b).im :=
    Real.log_lt_log (γ a).im_pos hh
  intro t ht
  have hpar : dist a t + dist t b = dist a b := by
    rw [Real.dist_eq, Real.dist_eq, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr ht.1), abs_of_nonpos (sub_nonpos.mpr ht.2),
      abs_of_nonpos (sub_nonpos.mpr hab.le)]
    ring
  have htri : dist (γ a) (γ t) + dist (γ t) (γ b) = dist (γ a) (γ b) := by
    rw [hmetric a ha t ht, hmetric t ht b hb, hmetric a ha b hb]
    exact hpar
  have hbetween := (upperHalfPlane_vertical_triangle_eq_iff (γ a) (γ t) (γ b)
    (ha0.trans hb0.symm)).mp htri
  rw [Set.uIcc_of_le hlog.le] at hbetween
  have htre : (γ t).re = 0 := hbetween.1.trans ha0
  have hd := hmetric a ha t ht
  rw [UpperHalfPlane.dist_of_re_eq (ha0.trans htre.symm), Real.dist_eq, Real.dist_eq,
    abs_of_nonpos (sub_nonpos.mpr hbetween.2.1),
    abs_of_nonpos (sub_nonpos.mpr ht.1)] at hd
  apply UpperHalfPlane.ext_re_im htre
  change (γ t).im = Real.exp (t + (Real.log (γ a).im - a))
  have htime : t + (Real.log (γ a).im - a) = Real.log (γ t).im := by linarith
  rw [htime, Real.exp_log (γ t).im_pos]

/-- Every actual locally unit-speed real curve is an SL-conjugate of the
vertical axis with a real parameter shift. An ordered endpoint verticalizer
chooses the orientation; no differentiability or quotient hypothesis is used. -/
theorem upperHalfPlane_locally_unit_speed_eq_conjugate_vertical
    (γ : ℝ → UpperHalfPlane)
    (hloc : ∀ t : ℝ, ∃ r > 0, ∀ s ∈ Metric.ball t r, ∀ u ∈ Metric.ball t r,
      dist (γ s) (γ u) = dist s u) :
    ∃ h : SL(2, ℝ), ∃ c : ℝ, ∀ t : ℝ,
      γ t = h • hyperbolicVerticalAxis (t + c) := by
  obtain ⟨r, hr, hmetric⟩ := hloc 0
  let a : ℝ := -r / 2
  let b : ℝ := r / 2
  have hab : a < b := by dsimp only [a, b]; linarith
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab.le⟩
  have hb : b ∈ Set.Icc a b := ⟨hab.le, le_rfl⟩
  have hball : Set.Icc a b ⊆ Metric.ball 0 r := by
    intro t ht
    change dist t 0 < r
    rw [Real.dist_eq, sub_zero, abs_lt]
    dsimp only [a, b] at ht
    constructor <;> linarith [ht.1, ht.2]
  have hne : γ a ≠ γ b := by
    intro he
    have hd := hmetric a (hball ha) b (hball hb)
    rw [he, dist_self] at hd
    exact hab.ne (dist_eq_zero.mp hd.symm)
  obtain ⟨h, ha0, hb0, hheight⟩ :=
    upperHalfPlane_distinct_pair_exists_ordered_verticalizer (γ a) (γ b) hne
  let δ : ℝ → UpperHalfPlane := fun t => h • γ t
  have hδmetric : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b,
      dist (δ s) (δ t) = dist s t := by
    intro s hs t ht
    change dist (h • γ s) (h • γ t) = dist s t
    rw [dist_smul]
    exact hmetric s (hball hs) t (hball ht)
  have hinterval := upperHalfPlane_vertical_interval_eq δ a b hab hδmetric ha0 hb0 hheight
  let c : ℝ := Real.log (δ a).im - a
  have hδloc : ∀ t : ℝ, ∃ r > 0, ∀ s ∈ Metric.ball t r, ∀ u ∈ Metric.ball t r,
      dist (δ s) (δ u) = dist s u := by
    intro t
    obtain ⟨R, hR, hdist⟩ := hloc t
    refine ⟨R, hR, ?_⟩
    intro s hs u hu
    change dist (h • γ s) (h • γ u) = dist s u
    rw [dist_smul]
    exact hdist s hs u hu
  have hδinit : ∃ t : ℝ, ∃ r > 0, ∀ s ∈ Metric.ball t r,
      δ s = hyperbolicVerticalAxis (s + c) := by
    refine ⟨0, r / 2, by linarith, ?_⟩
    intro s hs
    apply hinterval
    change dist s 0 < r / 2 at hs
    rw [Real.dist_eq, sub_zero, abs_lt] at hs
    dsimp only [a, b]
    constructor <;> linarith [hs.1, hs.2]
  have hglobal := upperHalfPlane_locally_unit_speed_vertical_continuation δ c hδloc hδinit
  refine ⟨h⁻¹, c, ?_⟩
  intro t
  have he := congrArg (fun z : UpperHalfPlane => h⁻¹ • z) (hglobal t)
  simpa only [δ, inv_smul_smul] using he

/-- Actual local unit-speed distance preservation on the real line implies
global hyperbolic distance preservation. -/
theorem upperHalfPlane_isometry_of_locally_unit_speed
    (γ : ℝ → UpperHalfPlane)
    (hloc : ∀ t : ℝ, ∃ r > 0, ∀ s ∈ Metric.ball t r, ∀ u ∈ Metric.ball t r,
      dist (γ s) (γ u) = dist s u) : Isometry γ := by
  obtain ⟨h, c, hc⟩ := upperHalfPlane_locally_unit_speed_eq_conjugate_vertical γ hloc
  apply Isometry.of_dist_eq
  intro s t
  rw [hc s, hc t, dist_smul, hyperbolicVerticalAxis_isometry.dist_eq,
    Real.dist_eq, Real.dist_eq]
  congr 1
  ring

end Markov
