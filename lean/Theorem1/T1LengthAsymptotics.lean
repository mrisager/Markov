import T1LengthVariable

/-! The genuine full length is between log x and four times log x for
large x. This coarse comparison suffices for both exact error scales. -/
noncomputable section
open Filter Asymptotics
namespace Markov

theorem t1_markovLength_log_bounds (x : ℝ) (hx : 3 ≤ x) :
    Real.log x ≤ t1_markovLength x ∧ t1_markovLength x ≤ 4*Real.log x := by
  have hx0 : 0 < x := by linarith
  have harg : x ≤ 3*x/2 + Real.sqrt ((3*x/2)^2-1) := by
    linarith [Real.sqrt_nonneg ((3*x/2)^2-1)]
  have hlo := Real.log_le_log hx0 harg
  change Real.log x ≤ Real.arcosh (3*x/2) at hlo
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hgap := (t1_arcosh_log_gap (3*x/2) (by linarith)).1
  have he : 2*(3*x/2) = 3*x := by ring
  rw [he,Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hx0.ne'] at hgap
  have hlog3 := Real.log_le_log (by norm_num : (0 : ℝ)<3) hx
  unfold t1_markovLength
  constructor <;> linarith

theorem t1_markovLength_tendsto : Tendsto t1_markovLength atTop atTop := by
  refine tendsto_atTop.2 (fun b => ?_)
  filter_upwards [eventually_ge_atTop (3 : ℝ),Real.tendsto_log_atTop.eventually_ge_atTop b]
    with x hx hb
  exact hb.trans (t1_markovLength_log_bounds x hx).1

theorem t1_markovLength_isBigO_log : t1_markovLength =O[atTop] Real.log := by
  apply IsBigO.of_bound 4
  filter_upwards [eventually_ge_atTop (3 : ℝ)] with x hx
  obtain ⟨hlo,hhi⟩ := t1_markovLength_log_bounds x hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  simpa only [Real.norm_eq_abs,abs_of_nonneg hlog,abs_of_nonneg (hlog.trans hlo)] using hhi

theorem t1_conditionalScale_log (x : ℝ) :
    conditionalScale x = primitiveConditionalScale (Real.log x) := rfl

theorem t1_unconditionalScale_log (x : ℝ) :
    unconditionalScale x = primitiveUnconditionalScale (Real.log x) := rfl

end Markov
