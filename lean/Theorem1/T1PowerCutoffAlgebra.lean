import T1RealCutoffSelection
import Markov.Transfer

/-! Exact power-cutoff algebra and eventual admissibility. This module
proves parameter facts only, and supplies no Mertens cancellation theorem. -/
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace Markov

theorem t1_cutoffExponent_lt_one (δ : ℝ) (hδ : 0 < δ) : cutoffExponent δ < 1 := by
  have hs := (cutoffExponent_spec δ hδ).2.1
  have hp : 0 < 1+δ := by linarith
  exact hs.trans ((div_lt_one hp).mpr (by linarith))

theorem t1_power_cutoff_quotient (R ε : ℝ) (hR : 0 < R) :
    R/(2*R^ε) = R^(1-ε)/2 := by
  rw [Real.rpow_sub hR,Real.rpow_one]
  ring

theorem t1_power_cutoff_tail_identity (R ε δ : ℝ) (hR : 0 < R) :
    R*R^ε*(R/(2*R^ε))^(-δ) = 2^δ*R^(1-δ+ε*(1+δ)) := by
  rw [t1_power_cutoff_quotient R ε hR,
    Real.div_rpow (Real.rpow_nonneg hR.le _) (by norm_num),
    ← Real.rpow_mul hR.le,Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),div_inv_eq_mul]
  have he : 1-δ+ε*(1+δ) = (1+ε)+(1-ε)*(-δ) := by ring
  rw [he,Real.rpow_add hR,Real.rpow_add hR,Real.rpow_one]
  ring

theorem t1_power_cutoff_head_identity (R ε : ℝ) (hR : 1 < R) (hε : 0 < ε) :
    R*(Real.log (R^ε))^(-(1 : ℝ)/2) =
      ε^(-(1 : ℝ)/2) * primitiveConditionalScale R := by
  have hR0 : 0 < R := by linarith
  have hlog : 0 ≤ Real.log R := (Real.log_pos hR).le
  rw [Real.log_rpow hR0,Real.mul_rpow hε.le hlog]
  rw [show -(1 : ℝ)/2 = -((1 : ℝ)/2) by ring,Real.rpow_neg hlog ((1 : ℝ)/2)]
  unfold primitiveConditionalScale
  change R*(ε^(-((1 : ℝ)/2))*((Real.log R)^((1 : ℝ)/2))⁻¹) =
    ε^(-((1 : ℝ)/2))*(R/((Real.log R)^((1 : ℝ)/2)))
  ring

theorem t1_powerCutoff_eventually_ge (ε : ℝ) (hε : ε < 1) (N : ℕ) :
    ∀ᶠ R : ℝ in atTop, N ≤ t1_realCutoff R (R^ε) := by
  have hexp : 0 < 1-ε := by linarith
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    (tendsto_rpow_atTop hexp).eventually_ge_atTop ((N : ℝ)+2)] with R hR hpow
  have hquot : R/(R^ε) = R^(1-ε) := by rw [Real.rpow_sub hR,Real.rpow_one]
  have hn : N+2 ≤ ⌊R/(R^ε)⌋₊ := by
    apply (Nat.le_floor_iff (by positivity : 0 ≤ R/(R^ε))).mpr
    rw [hquot]
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hpow
  unfold t1_realCutoff
  omega

theorem t1_powerCutoff_eventually_admissible (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (T : ℝ) (N : ℕ) :
    ∀ᶠ R : ℝ in atTop, 1 < R ∧ T ≤ R^ε ∧ 4*R^ε ≤ R ∧
      N ≤ t1_realCutoff R (R^ε) := by
  have he : 0 < 1-ε := by linarith
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (tendsto_rpow_atTop hε0).eventually_ge_atTop T,
    (tendsto_rpow_atTop he).eventually_ge_atTop 4,
    t1_powerCutoff_eventually_ge ε hε1 N] with R hR hT hpow hN
  refine ⟨hR,hT,?_,hN⟩
  have hR0 : 0 < R := by linarith
  have hquot : R/(R^ε) = R^(1-ε) := by rw [Real.rpow_sub hR0,Real.rpow_one]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hR0 ε)).mp
  rwa [hquot]

end Markov
