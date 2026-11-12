import T1VKDesmoothing
import T1VKPrimitiveEstimate
import T1QRHMertensPower

/-! Exact reduction of the only remaining input to the classical
zero-free region of the actual zeta function. No zero-free-region
estimate is assumed beyond the explicit argument of each theorem. -/
noncomputable section
open Filter
namespace Markov

theorem t1_mertens_vk_eventually_of_region (h : t1_VKZeroFreeRegion) :
    ∃ K d : ℝ, 0 < K ∧ 0 < d ∧ ∀ᶠ x : ℝ in atTop,
      |t1_mertens x| ≤ K*x*Real.exp (-d*t1_vkWeight x) := by
  obtain ⟨K,d,hK,hd,hR⟩ := t1_vkRieszMertens_eventual_bound h
  obtain ⟨X,hX⟩ := eventually_atTop.mp hR
  let k := t1_vkRieszOrder
  let A := t1_differenceWeightNorm k*K*(1+(k : ℝ))^(k+1)
  let B := t1_differenceBoundaryConstant k*((k : ℝ)+1)
  have hk : 0 < k := by norm_num [k,t1_vkRieszOrder]
  have hA : 0 ≤ A := by dsimp [A]; positivity [t1_differenceWeightNorm_nonneg k]
  have hB : 0 ≤ B := by dsimp [B]; positivity [t1_differenceBoundaryConstant_nonneg k]
  refine ⟨A+B+1,d/((k : ℝ)+1),by linarith,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (max X t1_vkHeightBase),
    t1_vkDesmoothingStep_eventual_bounds k hd] with x hx hh
  let step := t1_vkDesmoothingStep k d x
  have hXx : X ≤ x := (le_max_left _ _).trans hx
  have hxB : t1_vkHeightBase ≤ x := (le_max_right _ _).trans hx
  have hx0 := (Real.exp_pos (Real.exp 1)).trans_le hxB
  have hstep1 : 1 ≤ step := hh.1
  have hstepx : step ≤ x := hh.2
  have hstep := zero_lt_one.trans_le hstep1
  have hdif := t1_rieszDifference_vk_bound (k := k) hK.le hd hxB hstep.le hstepx
    (fun y hy => hX y (hXx.trans hy))
  have hM := t1_mertens_le_difference_div_add_error hk hx0.le hstep1
  have hbal : (x^(k+1)*Real.exp (-d*t1_vkWeight x))/step^k = step := by
    rw [← t1_vkDesmoothingStep_power k d x]
    change step^(k+1)/step^k = step
    rw [pow_succ,mul_div_cancel_left₀ _ (pow_ne_zero k hstep.ne')]
  have hD : |t1_rieszDifference k x step| / step^k ≤ A*step := calc
    _ ≤ (A*(x^(k+1)*Real.exp (-d*t1_vkWeight x)))/step^k :=
      div_le_div_of_nonneg_right hdif (by positivity)
    _ = _ := by rw [mul_div_assoc,hbal]
  calc
    _ ≤ A*step+B*step := hM.trans (add_le_add_left hD _)
    _ = (A+B)*step := by ring
    _ ≤ (A+B+1)*step := mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right zero_le_one) hstep.le
    _ = _ := by dsimp [step,t1_vkDesmoothingStep]; ring

theorem t1_mertens_vk_of_region (h : t1_VKZeroFreeRegion) : t1_MertensVKBound := by
  obtain ⟨K,d,hK,hd,hM⟩ := t1_mertens_vk_eventually_of_region h
  obtain ⟨X,hX⟩ := eventually_atTop.mp hM
  refine ⟨K,d,hK,hd,⌈X⌉₊,?_⟩
  intro n hn
  have hn' : X ≤ (n : ℝ) := (Nat.le_ceil X).trans (by exact_mod_cast hn)
  simpa only [t1_mertens,Nat.floor_natCast] using hX (n : ℝ) hn'

theorem t1_markovUnconditional_of_vk_region (h : t1_VKZeroFreeRegion) :
    UnconditionalBound t1_markovLeadingCoefficient :=
  t1_markovUnconditional_of_mertens_vk (t1_mertens_vk_of_region h)

theorem t1_mainTheorem_of_vk_region (h : t1_VKZeroFreeRegion) : MainTheorem :=
  t1_mainTheorem_of_mertens_estimates (t1_mertens_vk_of_region h) t1_QRH_implies_mertens_power

end Markov
