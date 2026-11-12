/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaVinogradovScheduledMargin
import T1ZetaPoleLogDerivative
import T1VKRawRegionInterface

/-! The actual classical zero-free region using the retained raw height
and the original scheduled quantitative Vinogradov growth estimate. -/

namespace RiemannGaussian.ZetaVinogradovZeroFree
open Filter ZetaVinogradovScheduledMargin
open scoped Topology

theorem exists_eventual_nonvanishing :
    ∃ T : ℝ, 4 ≤ T ∧ ∀ s : ℂ, T ≤ |s.im| →
      1-width s.im ≤ s.re → riemannZeta s ≠ 0 := by
  obtain ⟨K,hK,hreal⟩ := Markov.t1_neg_logDeriv_zeta_real_bounded
  obtain ⟨T,hT⟩ := eventually_atTop.mp (eventually_parameters hK)
  refine ⟨max 4 T,le_max_left _ _,fun s hs hσ => ?_⟩
  obtain ⟨hn,hheight,_,hwidth⟩ := hT _ ((le_max_right _ _).trans hs)
  obtain ⟨ho,hw⟩ := abs_invariance s.im
  rw [ho] at hn hheight hwidth
  have hwM : ZetaVinogradovMargin.width K (order s.im) |s.im| =
      ZetaVinogradovMargin.width K (order s.im) s.im := by
    simp only [ZetaVinogradovMargin.width,ZetaVinogradovMargin.reserve,
      ZetaVinogradovLocalDisc.profile,ZetaNearOneLogProfile.height,abs_mul,abs_abs]
  rw [hw,hwM] at hwidth
  exact ZetaVinogradovMargin.nonvanishing hK hreal (order s.im) hn s hheight (by linarith)

end RiemannGaussian.ZetaVinogradovZeroFree

namespace Markov

theorem t1_VKZeroFreeRegion_proved : t1_VKZeroFreeRegion := by
  obtain ⟨T,hT,h⟩ := RiemannGaussian.ZetaVinogradovZeroFree.exists_eventual_nonvanishing
  apply t1_VKZeroFreeRegion_of_raw (c := 1/19327352832) (T := T) (by norm_num) hT
  intro s hs hre
  have hw : RiemannGaussian.ZetaVinogradovScheduledMargin.width s.im =
      (1/19327352832 : ℝ)/t1_vkRawHeightDenom s.im := by
    unfold RiemannGaussian.ZetaVinogradovScheduledMargin.width
      RiemannGaussian.ZetaNearOneBudgetLimit.scale RiemannGaussian.ZetaNearOneLogProfile.height
      t1_vkRawHeightDenom
    simp only [div_div,mul_assoc]
  exact h s hs (by rwa [hw])

end Markov

-- Modified from David Sanftenberg’s RiemannGaussian for the Lean 4.28.0 certificate.
