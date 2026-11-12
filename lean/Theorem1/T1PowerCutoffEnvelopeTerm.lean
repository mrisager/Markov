import T1PowerCutoffAlgebra
import T1MertensPowerEnvelope

/-! The exact large-divisor term at the power cutoff. The bound on the
actual Mertens envelope is visible as a premise, not asserted here. -/
noncomputable section
namespace Markov

theorem t1_powerCutoff_envelope_term (R δ C : ℝ) (hR : 1 < R) (hδ : 0 < δ)
    (hC : 0 ≤ C) (hlarge : 4*R^(cutoffExponent δ) ≤ R)
    (hEnv : t1_mertensEnvelope (t1_realCutoff R (R^(cutoffExponent δ))) ≤
      C*(t1_realCutoff R (R^(cutoffExponent δ)) : ℝ)^(-δ)) :
    R*R^(cutoffExponent δ)*t1_mertensEnvelope (t1_realCutoff R (R^(cutoffExponent δ))) ≤
      C*2^δ*R^(1-δ/2) := by
  have hR0 : 0 < R := by linarith
  let ε := cutoffExponent δ
  let Y := R^ε
  let D := t1_realCutoff R Y
  have hY : 0 < Y := Real.rpow_pos_of_pos hR0 ε
  have hRY : 4 ≤ R/Y := (le_div_iff₀ hY).mpr hlarge
  have hb := t1_realCutoff_bounds R Y hY hRY
  have hbase : 0 < R/(2*Y) := div_pos hR0 (by positivity)
  have hpow := Real.rpow_le_rpow_of_nonpos hbase hb.2.1 (neg_nonpos.mpr hδ.le)
  have hid := t1_power_cutoff_tail_identity R ε δ hR0
  rw [(cutoffExponent_spec δ hδ).2.2] at hid
  calc
    _ ≤ R*Y*(C*(D : ℝ)^(-δ)) := mul_le_mul_of_nonneg_left hEnv (by positivity)
    _ = C*(R*Y*(D : ℝ)^(-δ)) := by ring
    _ ≤ C*(R*Y*(R/(2*Y))^(-δ)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpow (mul_nonneg hR0.le hY.le)) hC
    _ = _ := by
      change C*(R*R^ε*(R/(2*R^ε))^(-δ)) = _
      rw [hid]
      ring

end Markov
