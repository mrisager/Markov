import Markov.LogarithmicErrorScales
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic

/-! The original paper's logarithmic parameter choices and their purely
scalar admissibility and decay estimates. No geometric input is assumed. -/

noncomputable section
open Filter Asymptotics
open scoped Topology

namespace Markov

def theoremTwelveQ (R : ℝ) : ℝ := Real.log R ^ (2 : ℕ)
def theoremTwelveK (R : ℝ) : ℝ := Real.log R ^ (4 : ℕ)
def theoremTwelveH (κ R : ℝ) : ℝ := Real.log R / (4 * κ)
def theoremTwelveEta (R : ℝ) : ℝ := R ^ (-(1 / 2 : ℝ))

theorem theoremTwelveQ_tendsto : Tendsto theoremTwelveQ atTop atTop := by
  exact (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp Real.tendsto_log_atTop

theorem theoremTwelveK_tendsto : Tendsto theoremTwelveK atTop atTop := by
  exact (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).comp Real.tendsto_log_atTop

theorem theoremTwelveH_tendsto (κ : ℝ) (hκ : 0 < κ) :
    Tendsto (theoremTwelveH κ) atTop atTop :=
  Tendsto.atTop_div_const (by positivity : 0 < 4 * κ) Real.tendsto_log_atTop

/-- The exact corner exponential for the paper's height choice. -/
theorem theoremTwelve_corner_exp (κ R : ℝ) (hκ : 0 < κ) (hR : 0 < R) :
    Real.exp (-κ * theoremTwelveH κ R) = R ^ (-(1 / 4 : ℝ)) := by
  rw [Real.rpow_def_of_pos hR]
  congr 1
  dsimp [theoremTwelveH]
  field_simp

/-- The basic corner-gap condition holds eventually with the fixed epsilon `1`. -/
theorem theoremTwelve_eventually_basic (κ m : ℝ) (hκ : 0 < κ) (hm : 0 < m) :
    ∀ᶠ R : ℝ in atTop,
      3 * theoremTwelveEta R ≤ m * Real.exp (-κ * theoremTwelveH κ R) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually_ge_atTop (3 / m)] with R hR hpow
  have hthree : 3 ≤ m * R ^ (1 / 4 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hpow hm.le
    rw [mul_div_cancel₀ _ hm.ne'] at hh
    exact hh
  rw [theoremTwelve_corner_exp κ R hκ hR]
  dsimp [theoremTwelveEta]
  calc
    _ ≤ (m * R ^ (1 / 4 : ℝ)) * R ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hthree (Real.rpow_nonneg hR.le _)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hR]; norm_num

/-- All positivity and elementary size-order conditions hold above a fixed threshold. -/
theorem theoremTwelve_eventually_positive (κ A : ℝ) (hκ : 0 < κ) :
    ∀ᶠ R : ℝ in atTop, 1 < R ∧ 1 ≤ theoremTwelveQ R ∧
      theoremTwelveQ R < theoremTwelveK R ∧ A ≤ theoremTwelveH κ R ∧
      0 < theoremTwelveEta R := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_gt_atTop 1,
    (theoremTwelveH_tendsto κ hκ).eventually_ge_atTop A] with R hR hlog hH
  refine ⟨hR, ?_, ?_, hH, Real.rpow_pos_of_pos (by linarith) _⟩
  · dsimp [theoremTwelveQ]
    nlinarith
  · dsimp [theoremTwelveQ, theoremTwelveK]
    nlinarith [sq_nonneg (Real.log R ^ (2 : ℕ) - 1)]

/-- Every fixed logarithmic power is dominated by every positive real power. -/
theorem theoremTwelve_log_power_decay (p a : ℝ) (ha : 0 < a) :
    Tendsto (fun R : ℝ ↦ Real.log R ^ p * R ^ (-a)) atTop (𝓝 0) := by
  have hh := (isLittleO_log_rpow_rpow_atTop p ha).tendsto_div_nhds_zero
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [Real.rpow_neg hR.le, div_eq_mul_inv]

/-- The mollifier and exponent-three tail errors coincide for the exact paper choices. -/
theorem theoremTwelve_smoothing_tail_identity (R : ℝ) (hlog : Real.log R ≠ 0) :
    R * theoremTwelveQ R ^ (3 : ℕ) / theoremTwelveK R ^ (2 : ℕ) = R / Real.log R ^ (2 : ℕ) := by
  dsimp [theoremTwelveQ, theoremTwelveK]
  field_simp

/-- Any fixed power saving in `R` absorbs every fixed logarithmic power
against the paper's target scale. -/
theorem theoremTwelve_power_log_isLittleO (p a : ℝ) (ha : 0 < a) :
    (fun R : ℝ ↦ R ^ (1 - a) * Real.log R ^ p) =o[atTop]
      (fun R : ℝ ↦ R / Real.log R ^ (3 / 2 : ℝ)) := by
  have hh := (isLittleO_log_rpow_rpow_atTop (p + 3 / 2) ha).mul_isBigO
    (isBigO_refl (fun R : ℝ ↦ R ^ (1 - a) / Real.log R ^ (3 / 2 : ℝ)) atTop)
  apply hh.congr'
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with R hR
    have hRp : 0 < R := by linarith
    have hLp : 0 < Real.log R := Real.log_pos hR
    rw [Real.rpow_add hLp]
    field_simp
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with R hR
    have hRp : 0 < R := by linarith
    rw [← mul_div_assoc, ← Real.rpow_add hRp]
    congr 1
    rw [show a + (1 - a) = 1 by ring, Real.rpow_one]

/-- The unresolved exponential contribution has a fixed power saving for
the original logarithmic height and cutoff. -/
theorem theoremTwelve_exponential_error_isLittleO (κ c : ℝ) (hκ : 0 < κ) (hc : 0 < c) :
    (fun R : ℝ ↦ R * theoremTwelveK R * Real.exp (-c * theoremTwelveH κ R)) =o[atTop]
      (fun R : ℝ ↦ R / Real.log R ^ (3 / 2 : ℝ)) := by
  have hh := theoremTwelve_power_log_isLittleO 4 (c / (4 * κ)) (by positivity)
  apply hh.congr'
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with R hR
    have hRp : 0 < R := by linarith
    have he : Real.exp (-c * theoremTwelveH κ R) = R ^ (-(c / (4 * κ))) := by
      rw [Real.rpow_def_of_pos hRp]
      congr 1
      dsimp [theoremTwelveH]
      ring
    rw [he]
    dsimp [theoremTwelveK]
    rw [show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast]
    rw [Real.rpow_sub hRp, Real.rpow_one, Real.rpow_neg hRp.le]
    ring
  · exact Filter.EventuallyEq.rfl

/-- The exact paper choices satisfy all fixed lower thresholds, including
the inner smoothing radius threshold, with epsilon fixed to one. -/
theorem theoremTwelve_eventually_admissible (κ m H0 S0 C : ℝ)
    (hκ : 0 < κ) (hm : 0 < m) (hC : 0 ≤ C) :
    ∀ᶠ R : ℝ in atTop, 1 < R ∧ 1 ≤ theoremTwelveQ R ∧
      theoremTwelveQ R < theoremTwelveK R ∧ H0 ≤ theoremTwelveH κ R ∧
      0 < theoremTwelveEta R ∧
      3 * theoremTwelveEta R ≤ m * Real.exp (-κ * theoremTwelveH κ R) ∧
      S0 ≤ R - C / theoremTwelveQ R := by
  filter_upwards [theoremTwelve_eventually_positive κ H0 hκ,
    theoremTwelve_eventually_basic κ m hκ hm,
    eventually_ge_atTop (S0 + C)] with R hp hb hR
  have hQ : 0 < theoremTwelveQ R := by linarith [hp.2.1]
  have hd : C / theoremTwelveQ R ≤ C := by
    apply (div_le_iff₀ hQ).2
    nlinarith [hp.2.1]
  exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2, hb, by linarith⟩

/-- The angular counting error is negligible at the final logarithmic scale. -/
theorem theoremTwelve_angular_error_isLittleO :
    (fun R : ℝ ↦ Real.log (2 * theoremTwelveK R) / theoremTwelveEta R) =o[atTop]
      (fun R : ℝ ↦ R / Real.log R ^ (3 / 2 : ℝ)) := by
  have hpoly : (fun R : ℝ ↦ R ^ (1 / 2 : ℝ) * Real.log R) =o[atTop]
      (fun R : ℝ ↦ R / Real.log R ^ (3 / 2 : ℝ)) := by
    simpa only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, Real.rpow_one] using
      theoremTwelve_power_log_isLittleO 1 (1 / 2) (by norm_num)
  apply IsBigO.trans_isLittleO (g := fun R : ℝ ↦ R ^ (1 / 2 : ℝ) * Real.log R) _ hpoly
  apply IsBigO.of_bound 5
  filter_upwards [eventually_gt_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_gt_atTop 1] with R hR hL
  have hRp : 0 < R := by linarith
  have hLp : 0 < Real.log R := by linarith
  have hK : 1 ≤ theoremTwelveK R := one_le_pow₀ hL.le
  have hlogpos : 0 ≤ Real.log (2 * theoremTwelveK R) := Real.log_nonneg (by linarith)
  have hlogeq : Real.log (2 * theoremTwelveK R) = Real.log 2 + 4 * Real.log (Real.log R) := by
    rw [Real.log_mul (by norm_num) (by linarith : theoremTwelveK R ≠ 0), theoremTwelveK, Real.log_pow]
    norm_num
  have hlogle : Real.log (2 * theoremTwelveK R) ≤ 5 * Real.log R := by
    rw [hlogeq]
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have hll := Real.log_le_sub_one_of_pos hLp
    linarith
  have hEta : 0 ≤ theoremTwelveEta R := Real.rpow_nonneg hRp.le _
  rw [Real.norm_of_nonneg (div_nonneg hlogpos hEta),
    Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hRp.le _) hLp.le)]
  dsimp [theoremTwelveEta]
  rw [Real.rpow_neg hRp.le, div_eq_mul_inv, inv_inv]
  nlinarith [mul_le_mul_of_nonneg_right hlogle (Real.rpow_nonneg hRp.le (1 / 2 : ℝ))]


/-- The sum of all five scalar errors for the exact paper choices has
order `R/(log R)^(3/2)`. -/
theorem theoremTwelve_total_error_isBigO (κ c : ℝ) (hκ : 0 < κ) (hc : 0 < c) :
    (fun R : ℝ ↦ Real.log (2 * theoremTwelveK R) / theoremTwelveEta R +
      R / (theoremTwelveH κ R * Real.sqrt (theoremTwelveH κ R)) +
      R * theoremTwelveK R * Real.exp (-(c * theoremTwelveH κ R)) +
      R / theoremTwelveQ R + R * theoremTwelveQ R ^ (3 : ℕ) / theoremTwelveK R ^ (2 : ℕ))
      =O[atTop] (fun R : ℝ ↦ R / Real.log R ^ (3 / 2 : ℝ)) := by
  have hheight : (fun R : ℝ ↦ R / (theoremTwelveH κ R * Real.sqrt (theoremTwelveH κ R)))
      =O[atTop] (fun R : ℝ ↦ R / Real.log R ^ (3 / 2 : ℝ)) :=
    logarithmic_height_error_isBigO (4 * κ) (by positivity)
  have hsquare : (fun R : ℝ ↦ R / theoremTwelveQ R)
      =O[atTop] (fun R : ℝ ↦ R / Real.log R ^ (3 / 2 : ℝ)) :=
    logarithmic_square_error_isBigO
  have htail : (fun R : ℝ ↦ R * theoremTwelveQ R ^ (3 : ℕ) / theoremTwelveK R ^ (2 : ℕ))
      =O[atTop] (fun R : ℝ ↦ R / Real.log R ^ (3 / 2 : ℝ)) := by
    apply hsquare.congr'
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with R hR
      exact (theoremTwelve_smoothing_tail_identity R (Real.log_pos hR).ne').symm
    · exact Filter.EventuallyEq.rfl
  have hexp : (fun R : ℝ ↦ R * theoremTwelveK R * Real.exp (-(c * theoremTwelveH κ R)))
      =O[atTop] (fun R : ℝ ↦ R / Real.log R ^ (3 / 2 : ℝ)) := by
    simpa only [neg_mul] using (theoremTwelve_exponential_error_isLittleO κ c hκ hc).isBigO
  exact (((theoremTwelve_angular_error_isLittleO.isBigO.add hheight).add hexp).add hsquare).add htail

end Markov
