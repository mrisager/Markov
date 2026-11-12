import T1VKCutoffTerms
import T1FinalScaleTransfer

/-! Exact unconditional primitive and Markov rates from the explicit
Vinogradov–Korobov/Walfisz bound for the actual Mertens sum. -/
noncomputable section
open Filter Asymptotics
namespace Markov

theorem t1_primitiveUnconditional_of_mertens_vk (hM : t1_MertensVKBound) :
    (fun R => (t1_geometricPrimitiveCount R : ℝ) -
      t1_primitiveLeadingCoefficient*R^2) =O[atTop] primitiveUnconditionalScale := by
  obtain ⟨C,hC,T,_,hcut⟩ := t1_geometric_primitive_Y_cutoff
  obtain ⟨K,c,hK,hc,N,hEnv⟩ := t1_mertens_vk_implies_envelope hM
  have hsmall := (t1_vk_tail_isLittleO (c/4) (by positivity)).bound (c := 1) (by norm_num)
  apply IsBigO.of_bound (C*((c/4)^(-(1 : ℝ)/2)+K))
  filter_upwards [t1_vkCutoff_eventually_admissible c hc T N,
    t1_vkCutoff_tail K c hK hc N hEnv,eventually_gt_atTop (Real.exp 1),hsmall]
    with R hR htail hlarge hsmallR
  have hR0 := (Real.exp_pos _).trans hlarge
  have hscale := t1_primitiveUnconditionalScale_pos R hlarge
  have hexp : R*Real.exp (-(c/4)*t1_vkWeight R) ≤ primitiveUnconditionalScale R := by
    simpa only [Real.norm_eq_abs,abs_of_pos (mul_pos hR0 (Real.exp_pos _)),
      abs_of_pos hscale,one_mul] using hsmallR
  simp only [Real.norm_eq_abs,abs_of_pos hscale]
  calc
    _ ≤ C * (R*(Real.log (t1_vkY c R))^(-(1 : ℝ)/2) +
        R*t1_vkY c R*t1_mertensEnvelope (t1_realCutoff R (t1_vkY c R))) :=
      hcut R (t1_vkY c R) hR.1 hR.2.1
    _ ≤ C*((c/4)^(-(1 : ℝ)/2)*primitiveUnconditionalScale R +
        K*primitiveUnconditionalScale R) := by
      rw [t1_vkCutoff_head c R hc hlarge]
      exact mul_le_mul_of_nonneg_left
        (add_le_add_right (htail.trans (mul_le_mul_of_nonneg_left hexp hK.le)) _) hC.le
    _ = _ := by ring

theorem t1_markovUnconditional_of_mertens_vk (hM : t1_MertensVKBound) :
    UnconditionalBound t1_markovLeadingCoefficient :=
  t1_markovUnconditional_of_primitive (t1_primitiveUnconditional_of_mertens_vk hM)

/-- Both exact statements reduce to the two explicit arithmetic estimates.
This is a reduction, not an unconditional proof of Theorem 1. -/
theorem t1_mainTheorem_of_mertens_estimates (hVK : t1_MertensVKBound)
    (hPower : QuasiRiemannHypothesis → ∃ δ : ℝ, 0 < δ ∧ t1_MertensPowerBound δ) :
    MainTheorem := by
  refine ⟨t1_markovLeadingCoefficient,t1_markovLeadingCoefficient_pos,
    t1_markovUnconditional_of_mertens_vk hVK,?_⟩
  intro hQRH
  obtain ⟨δ,hδ,hM⟩ := hPower hQRH
  exact t1_markovConditional_of_mertens_power δ hδ hM

end Markov
