import T1RealCutoffSelection

/-! The real-parameter form of the genuine geometric primitive cutoff.
The selected integer divisor bound is computed, with all floor inequalities. -/
noncomputable section
namespace Markov

theorem t1_geometric_primitive_Y_cutoff :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 1 < T ∧
      ∀ R Y : ℝ, T ≤ Y → 4*Y ≤ R →
        |(t1_geometricPrimitiveCount R : ℝ) -
          (6*modularMcShaneRivinArea/Real.pi^2)*R^2| ≤
          C * (R * (Real.log Y)^(-(1 : ℝ)/2) +
            R*Y*t1_mertensEnvelope (t1_realCutoff R Y)) := by
  obtain ⟨C,hC,T,hT,hcut⟩ := t1_geometric_primitive_cutoff_bound
  refine ⟨2*C,by positivity,T,hT,?_⟩
  intro R Y hY hlarge
  have hY1 : 1 < Y := hT.trans_le hY
  have hY0 : 0 < Y := by linarith
  have hR : 0 < R := by linarith
  have hRY : 4 ≤ R/Y := (le_div_iff₀ hY0).mpr hlarge
  let D := t1_realCutoff R Y
  have hDb := t1_realCutoff_bounds R Y hY0 hRY
  have hrad := t1_realCutoff_radius R Y hY0 hRY
  have hbd := hcut R hR D hDb.1 (hY.trans hrad)
  have hlogY : 0 < Real.log Y := Real.log_pos hY1
  have hlog : Real.log Y ≤ t1_headLog R ((D : ℝ)+1) := by
    rw [t1_headLog,← Real.log_div hR.ne' (by positivity : (D : ℝ)+1 ≠ 0)]
    exact Real.log_le_log hY0 hrad
  have hpow := Real.rpow_le_rpow_of_nonpos hlogY hlog (by norm_num : (-(1 : ℝ)/2) ≤ 0)
  have hhead : R * (t1_headLog R ((D : ℝ)+1))^(-(1 : ℝ)/2) ≤
      R*(Real.log Y)^(-(1 : ℝ)/2) := mul_le_mul_of_nonneg_left hpow hR.le
  have hratio : R/(D : ℝ) ≤ 2*Y := t1_realCutoff_ratio R Y hY0 hRY
  have htail : R*(R/(D : ℝ))*t1_mertensEnvelope D ≤
      2*(R*Y*t1_mertensEnvelope D) := by
    have hm := mul_le_mul_of_nonneg_left hratio hR.le
    have hm' := mul_le_mul_of_nonneg_right hm (t1_mertensEnvelope_nonneg D)
    nlinarith
  have ha : 0 ≤ R*(Real.log Y)^(-(1 : ℝ)/2) :=
    mul_nonneg hR.le (Real.rpow_nonneg hlogY.le _)
  calc
    _ ≤ C * (R*(Real.log Y)^(-(1 : ℝ)/2) +
        2*(R*Y*t1_mertensEnvelope D)) :=
      hbd.trans (mul_le_mul_of_nonneg_left (add_le_add hhead htail) hC.le)
    _ ≤ _ := by
      change _ ≤ (2*C)*(R*(Real.log Y)^(-(1 : ℝ)/2)+R*Y*t1_mertensEnvelope D)
      nlinarith [mul_nonneg hC.le ha]

end Markov
