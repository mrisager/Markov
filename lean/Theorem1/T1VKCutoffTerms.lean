import T1VKCutoffSelection
import T1VKScaleAlgebra
import T1MertensVKEnvelope

/-! Evaluation of the two cutoff terms, using the actual VK envelope
only as an explicit premise. -/
noncomputable section
open Filter Asymptotics
namespace Markov

theorem t1_vkCutoff_head (c R : ℝ) (hc : 0 < c) (hR : Real.exp 1 < R) :
    R*(Real.log (t1_vkY c R))^(-(1 : ℝ)/2) =
      (c/4)^(-(1 : ℝ)/2)*primitiveUnconditionalScale R := by
  have hc4 : 0 < c/4 := by positivity
  have hW := t1_vkWeight_pos R hR
  have he : -(1 : ℝ)/2 = -((1 : ℝ)/2) := neg_div _ _
  rw [t1_vkY,Real.log_exp,show c*t1_vkWeight R/4 = (c/4)*t1_vkWeight R by ring,
    Real.mul_rpow hc4.le hW.le,t1_primitiveUnconditionalScale_vkWeight R hR,he,
    Real.rpow_neg hW.le]
  ring

theorem t1_vkCutoff_tail (C c : ℝ) (hC : 0 < C) (hc : 0 < c) (N : ℕ)
    (hEnv : ∀ D : ℕ, N ≤ D → t1_mertensEnvelope D ≤ C*Real.exp (-c*t1_vkWeight D)) :
    ∀ᶠ R : ℝ in atTop, R*t1_vkY c R*t1_mertensEnvelope (t1_realCutoff R (t1_vkY c R)) ≤
      C*(R*Real.exp (-(c/4)*t1_vkWeight R)) := by
  have hhalf := tendsto_rpow_atTop (show (0 : ℝ)<(1 : ℝ)/2 by norm_num)
  filter_upwards [t1_vkCutoff_eventually_admissible c hc 1 N,
    hhalf.eventually_ge_atTop (Real.exp (Real.exp 1)),eventually_gt_atTop (Real.exp 2)]
    with R hcut hhalfR hR
  let D := t1_realCutoff R (t1_vkY c R)
  have hR0 := (Real.exp_pos _).trans hR
  have hY : 0 < t1_vkY c R := Real.exp_pos _
  have hweight := (t1_vkWeight_half_log R hR).trans
    (t1_vkWeight_monotone hhalfR (hhalfR.trans hcut.2.2.1) hcut.2.2.1)
  have hexp : Real.exp (-c*t1_vkWeight D) ≤ Real.exp (-c*t1_vkWeight R/2) := by
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ -c*(t1_vkWeight R/2) := mul_le_mul_of_nonpos_left hweight (by linarith)
      _ = _ := by ring
  have htail := (hEnv D hcut.2.2.2).trans (mul_le_mul_of_nonneg_left hexp hC.le)
  calc
    _ ≤ R*t1_vkY c R*(C*Real.exp (-c*t1_vkWeight R/2)) :=
      mul_le_mul_of_nonneg_left htail (mul_nonneg hR0.le hY.le)
    _ = C*(R*(Real.exp (c*t1_vkWeight R/4)*Real.exp (-c*t1_vkWeight R/2))) := by
      unfold t1_vkY
      ring
    _ = _ := by rw [← Real.exp_add]; congr 3; ring

end Markov
