import T1VKReciprocalBound
import T1RieszStripIntegrand

/-! The literal analytic inputs on the moving region, derived from the
explicit zero-free hypothesis. The smoothing order is fixed at thirty. -/
noncomputable section
open Complex Set
namespace Markov

def t1_vkRieszOrder : ℕ := 30

theorem t1_vk_reciprocalZeta_differentiableAt {c : ℝ} (hc : 0 < c)
    (hZ : ∀ s : ℂ, 1-t1_vkHeightWidth c s.im ≤ s.re → t1_poleRemovedZeta s ≠ 0)
    {s : ℂ} (hs : t1_vkContourLeft c s.im ≤ s.re) :
    DifferentiableAt ℂ t1_reciprocalZeta s := by
  have hd := t1_vkDiskWidth_pos hc s.im
  have hW : t1_vkDiskWidth c s.im ≤ t1_vkHeightWidth c s.im := by
    apply t1_vkHeightWidth_antitone_abs hc.le
    rw [abs_of_nonneg (by positivity : 0 ≤ |s.im|+1)]
    linarith
  unfold t1_vkContourLeft at hs
  exact (differentiableAt_id.sub_const 1).div
    (t1_poleRemovedZeta_differentiable s) (hZ s (by linarith))

theorem t1_vkRieszIntegrand_differentiableAt {c : ℝ} (hc : 0 < c) (hc' : c ≤ 1/4)
    (hZ : ∀ s : ℂ, 1-t1_vkHeightWidth c s.im ≤ s.re → t1_poleRemovedZeta s ≠ 0)
    {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : t1_vkContourLeft c s.im ≤ s.re) :
    DifferentiableAt ℂ (t1_rieszIntegrand t1_vkRieszOrder x t1_reciprocalZeta) s := by
  have hσ := (t1_vkContourLeft_bounds hc hc' s.im).1.trans hs
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (x : ℂ)^z) s :=
    differentiableAt_id.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  exact (hpow.mul (t1_vk_reciprocalZeta_differentiableAt hc hZ hs)).mul
    ((t1_rieszDenom_differentiable _ s).inv (t1_rieszDenom_ne_zero _ (by linarith)))

theorem t1_vkRieszIntegrand_norm {c C : ℝ} (hc : 0 < c) (hc' : c ≤ 1/4) (hC : 0 ≤ C)
    (hB : ∀ s : ℂ, t1_vkContourLeft c s.im ≤ s.re →
      ‖t1_reciprocalZeta s‖ ≤ C*(1+|s.im|)^27)
    {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : t1_vkContourLeft c s.im ≤ s.re) :
    ‖t1_rieszIntegrand t1_vkRieszOrder x t1_reciprocalZeta s‖ ≤
      (x^s.re*C*(3 : ℝ)^31)*(1+|s.im|)^(-(4 : ℝ)) := by
  have hb : ‖t1_reciprocalZeta s‖ ≤ C*(1+|s.im|)^(27 : ℝ) := by
    simpa only [← Nat.cast_ofNat (R := ℝ),Real.rpow_natCast] using hB s hs
  have hn := t1_rieszIntegrand_norm_le hx hC
    ((t1_vkContourLeft_bounds hc hc' s.im).1.trans hs) hb (k := t1_vkRieszOrder)
  rw [show (27 : ℝ)-((t1_vkRieszOrder : ℝ)+1) = -4 by norm_num [t1_vkRieszOrder],
    t1_vkRieszOrder] at hn
  exact hn

theorem t1_vkRieszIntegrand_right_strip {c C b : ℝ} (hc : 0 < c) (hc' : c ≤ 1/4)
    (hb : 1 ≤ b)
    (hZ : ∀ s : ℂ, 1-t1_vkHeightWidth c s.im ≤ s.re → t1_poleRemovedZeta s ≠ 0)
    (hB : ∀ s : ℂ, t1_vkContourLeft c s.im ≤ s.re →
      ‖t1_reciprocalZeta s‖ ≤ C*(1+|s.im|)^27) :
    DifferentiableOn ℂ t1_reciprocalZeta {s : ℂ | s.re ∈ Icc b 2} ∧
      ∀ s : ℂ, s.re ∈ Icc b 2 → ‖t1_reciprocalZeta s‖ ≤ C*(1+|s.im|)^(27 : ℝ) := by
  have hleft (s : ℂ) (hs : s.re ∈ Icc b 2) : t1_vkContourLeft c s.im ≤ s.re :=
    ((t1_vkContourLeft_bounds hc hc' s.im).2.le.trans hb).trans hs.1
  refine ⟨fun s hs => (t1_vk_reciprocalZeta_differentiableAt hc hZ (hleft s hs)).differentiableWithinAt,?_⟩
  intro s hs
  simpa only [← Nat.cast_ofNat (R := ℝ),Real.rpow_natCast] using hB s (hleft s hs)

end Markov
