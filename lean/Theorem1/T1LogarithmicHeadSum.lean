import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! A discrete-to-integral estimate for the small-divisor logarithmic
kernel, obtained by comparing the terms on individual cells. -/

noncomputable section
open Classical Finset Set MeasureTheory
namespace Markov

def t1_headLog (R x : ℝ) : ℝ := Real.log R - Real.log x

def t1_headWeight (R x : ℝ) : ℝ := x⁻¹ * (t1_headLog R x) ^ (-(3 : ℝ) / 2)

theorem t1_headLog_pos_on (R b : ℝ) (hlog : 0 < t1_headLog R b)
    {x : ℝ} (hx : x ∈ Set.Icc 1 b) : 0 < t1_headLog R x := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
  have hlogmono := Real.log_le_log hxpos hx.2
  unfold t1_headLog at hlog ⊢
  linarith

theorem t1_headWeight_continuousOn (R b : ℝ) (hlog : 0 < t1_headLog R b) :
    ContinuousOn (t1_headWeight R) (Set.Icc 1 b) := by
  intro x hx
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
  have hell := t1_headLog_pos_on R b hlog hx
  apply ContinuousAt.continuousWithinAt
  exact (continuousAt_inv₀ hxpos.ne').mul
    ((continuousAt_const.sub (Real.continuousAt_log hxpos.ne')).rpow_const (Or.inl hell.ne'))

theorem t1_headWeight_antiderivative (R x : ℝ) (hx : 0 < x) (hlog : 0 < t1_headLog R x) :
    HasDerivAt (fun t => 2 * (t1_headLog R t) ^ (-(1 : ℝ) / 2)) (t1_headWeight R x) x := by
  have hell : HasDerivAt (t1_headLog R) (-x⁻¹) x := by
    simpa only [t1_headLog, zero_sub] using
      (hasDerivAt_const x (Real.log R)).sub (Real.hasDerivAt_log hx.ne')
  have h := (hell.rpow_const (p := -(1 : ℝ) / 2) (Or.inl hlog.ne')).const_mul 2
  convert h using 1
  dsimp [t1_headWeight]
  norm_num
  ring

/-- Each grid value is bounded by twice the kernel throughout the next
unit cell. Only positivity of the logarithms is needed. -/
theorem t1_headWeight_cell_bound (R g x : ℝ) (hg : 1 ≤ g)
    (hx : g ≤ x ∧ x ≤ g + 1) (hlogx : 0 < t1_headLog R x) :
    t1_headWeight R g ≤ 2 * t1_headWeight R x := by
  have hgpos : 0 < g := lt_of_lt_of_le zero_lt_one hg
  have hxpos : 0 < x := hgpos.trans_le hx.1
  have hlogorder : t1_headLog R x ≤ t1_headLog R g := by
    unfold t1_headLog
    exact sub_le_sub_left (Real.log_le_log hgpos hx.1) _
  have hpow := Real.rpow_le_rpow_of_nonpos hlogx hlogorder
    (show -(3 : ℝ) / 2 ≤ 0 by norm_num)
  have hginv : g⁻¹ ≤ 2 * x⁻¹ := by
    have hx2 : x ≤ 2 * g := by linarith
    have hdiv : (1 : ℝ) / g ≤ 2 / x :=
      (div_le_div_iff₀ hgpos hxpos).mpr (by simpa only [one_mul] using hx2)
    simpa only [one_div, div_eq_mul_inv, one_mul] using hdiv
  calc
    _ ≤ (2 * x⁻¹) * (t1_headLog R x) ^ (-(3 : ℝ) / 2) :=
      mul_le_mul hginv hpow (Real.rpow_nonneg (hlogx.le.trans hlogorder) _)
        (mul_nonneg (by norm_num) (inv_nonneg.mpr hxpos.le))
    _ = _ := by unfold t1_headWeight; ring

/-- The small-divisor kernel has a square-root-log bound, with a precise
one-cell endpoint. The endpoint shift will later be absorbed in the cutoff
parameter choice. -/
theorem t1_logarithmic_head_weight_sum (R : ℝ) (D : ℕ)
    (hlog : 0 < t1_headLog R (D + 1)) :
    (∑ g ∈ Finset.Icc 1 D, t1_headWeight R g) ≤
      4 * (t1_headLog R (D + 1)) ^ (-(1 : ℝ) / 2) := by
  have hb : (1 : ℝ) ≤ D + 1 := by linarith [Nat.cast_nonneg (α := ℝ) D]
  have hcont := t1_headWeight_continuousOn R (D + 1) hlog
  have hint : IntervalIntegrable (t1_headWeight R) volume 1 (D + 1) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hb]
    exact hcont.integrableOn_Icc
  have hprimitive : (∫ x in (1 : ℝ)..(D + 1), t1_headWeight R x) =
      2 * (t1_headLog R (D + 1)) ^ (-(1 : ℝ) / 2) -
      2 * (t1_headLog R 1) ^ (-(1 : ℝ) / 2) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => 2 * (t1_headLog R t) ^ (-(1 : ℝ) / 2)) _ hint
    intro x hx
    rw [Set.uIcc_of_le hb] at hx
    exact t1_headWeight_antiderivative R x (lt_of_lt_of_le zero_lt_one hx.1)
      (t1_headLog_pos_on R (D + 1) hlog hx)
  have hcells : ∀ i ∈ Finset.Ico 1 (D + 1), ∀ x ∈ Set.Ico (i : ℝ) (i + 1 : ℕ),
      t1_headWeight R i ≤ 2 * t1_headWeight R x := by
    intro i hi x hx
    obtain ⟨hi1, hiD⟩ := Finset.mem_Ico.mp hi
    have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi1
    have hxI : x ∈ Set.Icc 1 (D + 1 : ℝ) := by
      refine ⟨hiR.trans hx.1, ?_⟩
      have hupper : (i + 1 : ℕ) ≤ D + 1 := by omega
      exact hx.2.le.trans (by exact_mod_cast hupper)
    apply t1_headWeight_cell_bound R i x hiR
    · exact ⟨hx.1, by exact_mod_cast hx.2.le⟩
    · exact t1_headLog_pos_on R (D + 1) hlog hxI
  have hsum := sum_Ico_le_integral_of_le (a := 1) (b := D + 1)
    (f := t1_headWeight R) (g := fun x => 2 * t1_headWeight R x)
    (by omega) (fun i hi => hcells i (Finset.mem_Ico.mpr (Set.mem_Ico.mp hi)))
    (((continuousOn_const.mul hcont).integrableOn_Icc).mono_set (by
      intro x hx
      simpa only [Nat.cast_add, Nat.cast_one] using Set.Ico_subset_Icc_self hx))
  have hset : Finset.Ico 1 (D + 1) = Finset.Icc 1 D := by
    ext g
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  simp only [Nat.cast_add, Nat.cast_one] at hsum
  rw [hset, intervalIntegral.integral_const_mul, hprimitive] at hsum
  have hnonneg : 0 ≤ (t1_headLog R 1) ^ (-(1 : ℝ) / 2) :=
    Real.rpow_nonneg (t1_headLog_pos_on R (D + 1) hlog
      (show (1 : ℝ) ∈ Set.Icc 1 (D + 1 : ℝ) from ⟨le_rfl, hb⟩)).le _
  nlinarith

end Markov
